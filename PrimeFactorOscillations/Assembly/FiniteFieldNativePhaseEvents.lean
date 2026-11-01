/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeVanishingProfiles
import PrimeFactorOscillations.Helpers.NativePrimePhaseCycles

/-! # The common quadratic field phase and complete native cycle constraints -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeQuadraticPhase (ell : Nat) : Real :=
  (numeratorKernel (-1) ell).re

def nativeQuadraticPhaseEvent (b : Bool) (ell : Nat) : Prop :=
  nativeQuadraticPhase ell = nativeWordSign b

def nativePhaseBand (b : Bool) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if nativeQuadraticPhaseEvent b ell then 1 else 0))

def nativePhaseProfileCompatible (P : Finset Nat) (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (b : Bool) : Prop :=
  forall C : Finset (Prod Nat Nat), Membership.mem (nativeEulerianMasks P G) C ->
    nativeVanishingProfileCoefficient C a = nativeWordSign b ^ C.card

def nativePhaseProfileEvent (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (b : Bool) (ell : Nat) : Prop :=
  And (nativeQuadraticPhaseEvent b ell) (nativeVanishingProfileEvent G a ell)

def nativePhaseProfileMass (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (b : Bool) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if nativePhaseProfileEvent G a b ell then 1 else 0))

def nativePhaseProfileRate (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (b : Bool) : Real :=
  (1 / (2 : Real) ^ (G.card + 1)) * G.powerset.sum (fun C =>
    nativeVanishingProfileCoefficient C a *
      (numeratorPrincipalIndicator (nativeSignedRowProduct C C) +
        nativeWordSign b * numeratorPrincipalIndicator (-nativeSignedRowProduct C C)))

theorem native_quadratic_phase_square_one (ell : Nat)
    (hell : Nat.Prime ell) (hell2 : 2 < ell) : nativeQuadraticPhase ell ^ 2 = 1 := by
  let : Fact (Nat.Prime ell) := Fact.mk hell
  have hn : Not (((-1 : Int) : ZMod ell) = 0) := by
    simpa only [Int.cast_neg, Int.cast_one] using
      (neg_ne_zero.mpr (one_ne_zero : Not ((1 : ZMod ell) = 0)))
  exact real_kernel_square_of_nonzero (-1) ell hell2 hn

theorem native_real_kernel_power (D : Int) (n ell : Nat) (hodd : Odd ell) :
    (numeratorKernel (D ^ n) ell).re = (numeratorKernel D ell).re ^ n := by
  simpa only [Finset.prod_const, Finset.card_range] using
    real_kernel_finset_product (Finset.range n) (fun _ => D) ell hodd

theorem native_paired_product_square_one (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P)
    (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    (C.prod (fun e =>
      (numeratorKernel (nativeSignedLowerCoefficient e) ell).re *
        (numeratorKernel (nativeSignedUpperCoefficient e) ell).re)) ^ 2 = 1 := by
  rw [<- Finset.prod_pow]
  calc
    _ = C.prod (fun _ => (1 : Real)) := by
      apply Finset.prod_congr rfl
      intro e he
      have hs := native_signed_edge_kernel_squares P hP e (hC he) ell hell hell2 hlarge
      rw [mul_pow, hs.1, hs.2]
      norm_num
    _ = 1 := by simp

theorem native_cycle_phase_product (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    C.prod (fun e =>
      (numeratorKernel (nativeSignedLowerCoefficient e) ell).re *
        (numeratorKernel (nativeSignedUpperCoefficient e) ell).re) =
      nativeQuadraticPhase ell ^ C.card := by
  let r := C.prod (fun e => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) *
    C.prod (fun e => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re)
  let u := nativeQuadraticPhase ell ^ C.card
  have hr : r ^ 2 = 1 := by
    simpa only [r, Finset.prod_mul_distrib] using
      native_paired_product_square_one P hP C hC ell hell hell2 hlarge
  have hphase := native_quadratic_phase_square_one ell hell hell2
  have hu : u ^ 2 = 1 := by
    dsimp only [u]
    calc
      _ = nativeQuadraticPhase ell ^ (C.card * 2) := (pow_mul _ _ _).symm
      _ = nativeQuadraticPhase ell ^ (2 * C.card) := by rw [Nat.mul_comm C.card 2]
      _ = (nativeQuadraticPhase ell ^ 2) ^ C.card := pow_mul _ _ _
      _ = 1 := by rw [hphase, one_pow]
  have hsq : IsSquare ((-1 : Int) ^ C.card * nativeSignedRowProduct C C) :=
    (native_signed_phase_diagonal_isSquare_iff P hP C hC C.card).mpr
      (And.intro hdeg (by omega))
  have hodd := hell.odd_of_ne_two (by omega)
  have hid :
      (numeratorKernel ((-1 : Int) ^ C.card * nativeSignedRowProduct C C) ell).re = u * r := by
    rw [real_kernel_mul, native_real_kernel_power (-1) C.card ell hodd,
      nativeSignedRowProduct, real_kernel_mul,
      real_kernel_finset_product C nativeSignedLowerCoefficient ell hodd,
      real_kernel_finset_product C nativeSignedUpperCoefficient ell hodd]
    rfl
  choose k hk using hsq
  have hn : 0 <= u * r := by
    rw [<- hid, hk, real_kernel_mul]
    exact mul_self_nonneg _
  have hsq1 : (u * r) ^ 2 = 1 := by rw [mul_pow, hu, hr]; norm_num
  have hz : (u * r - 1) * (u * r + 1) = 0 := by nlinarith only [hsq1]
  have hone : u * r = 1 := by
    rcases mul_eq_zero.mp hz with h | h
    . exact sub_eq_zero.mp h
    . linarith only [h, hn]
  have heq : r = u := by
    calc
      r = u ^ 2 * r := by rw [hu, one_mul]
      _ = u * (u * r) := by ring
      _ = u := by rw [hone, mul_one]
  simpa only [r, u, Finset.prod_mul_distrib] using heq

theorem native_vanishing_profile_mask_product (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hevent : nativeVanishingProfileEvent G a ell) :
    nativeVanishingProfileCoefficient C a =
      C.prod (fun e =>
        (numeratorKernel (nativeSignedLowerCoefficient e) ell).re *
          (numeratorKernel (nativeSignedUpperCoefficient e) ell).re) := by
  unfold nativeVanishingProfileCoefficient
  apply Finset.prod_congr rfl
  intro e he
  have hg := hCG he
  have hu := native_signed_edge_kernel_squares P hP e (hG hg) ell hell hell2 hlarge
  have ht := native_trace_eq_signed_rows e.1 e.2 ell
    ((native_gap_edges_mem_iff P e).mp (hG hg)).2.2
  have hs := hevent e hg
  rw [ht] at hs
  exact ((native_trace_status_iff_paired_sign (a e) _ _ hu.1 hu.2).mp hs).symm

theorem native_phase_profile_event_compatible (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) (ell : Nat)
    (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hevent : nativePhaseProfileEvent G a b ell) :
    nativePhaseProfileCompatible P G a b := by
  intro C hC
  have hc := (native_eulerian_masks_mem_iff P G C).mp hC
  have hp : nativeQuadraticPhase ell = nativeWordSign b := hevent.1
  rw [native_vanishing_profile_mask_product P hP G hG a C hc.1 ell hell hell2
    hlarge hevent.2, native_cycle_phase_product P hP C (hc.1.trans hG) hc.2
      ell hell hell2 hlarge, hp]

theorem native_phase_profile_pointwise_selector (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) (ell : Nat)
    (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    (if nativePhaseProfileEvent G a b ell then (1 : Real) else 0) =
      nativeWordBit b (nativeQuadraticPhase ell) *
        G.prod (fun e => nativeWordBit (a e)
          ((numeratorKernel (nativeSignedLowerCoefficient e) ell).re *
            (numeratorKernel (nativeSignedUpperCoefficient e) ell).re)) := by
  rw [native_word_bit_eq_indicator b (nativeQuadraticPhase ell)
      (native_quadratic_phase_square_one ell hell hell2),
    <- native_vanishing_profile_pointwise_selector P hP G hG a ell hell hell2 hlarge]
  by_cases hp : nativeQuadraticPhase ell = nativeWordSign b
  . by_cases hv : nativeVanishingProfileEvent G a ell
    . have hj : nativePhaseProfileEvent G a b ell := And.intro hp hv
      rw [ite_eq_left hj, ite_eq_left hp, ite_eq_left hv]
      norm_num
    . have hn : Not (nativePhaseProfileEvent G a b ell) := fun h => hv h.2
      rw [ite_eq_right hn, ite_eq_left hp, ite_eq_right hv]
      norm_num
  . by_cases hv : nativeVanishingProfileEvent G a ell
    . have hn : Not (nativePhaseProfileEvent G a b ell) := fun h => hp h.1
      rw [ite_eq_right hn, ite_eq_right hp, ite_eq_left hv]
      norm_num
    . have hn : Not (nativePhaseProfileEvent G a b ell) := fun h => hp h.1
      rw [ite_eq_right hn, ite_eq_right hp, ite_eq_right hv]
      norm_num

theorem native_quadratic_phase_odd_power (ell : Nat) (hell : Nat.Prime ell)
    (hell2 : 2 < ell) (n : Nat) (hn : n % 2 = 1) :
    nativeQuadraticPhase ell ^ n = nativeQuadraticPhase ell := by
  have he : n = 2 * (n / 2) + 1 := by omega
  rw [he, pow_add, pow_mul, native_quadratic_phase_square_one ell hell hell2,
    one_pow, pow_one, one_mul]

theorem native_odd_cycle_phase_readout (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hcard : C.card % 2 = 1) (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    C.prod (fun e =>
      (numeratorKernel (nativeSignedLowerCoefficient e) ell).re *
        (numeratorKernel (nativeSignedUpperCoefficient e) ell).re) =
      nativeQuadraticPhase ell := by
  rw [native_cycle_phase_product P hP C hC hdeg ell hell hell2 hlarge,
    native_quadratic_phase_odd_power ell hell hell2 C.card hcard]

theorem native_odd_mask_profile_reads_phase (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hcard : C.card % 2 = 1) (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hevent : nativeVanishingProfileEvent G a ell) :
    nativeVanishingProfileCoefficient C a = nativeQuadraticPhase ell := by
  rw [native_vanishing_profile_mask_product P hP G hG a C hCG ell hell hell2
    hlarge hevent, native_odd_cycle_phase_readout P hP C (hCG.trans hG) hdeg
      hcard ell hell hell2 hlarge]

theorem native_phase_profile_pointwise_expansion (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) (ell : Nat)
    (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    (if nativePhaseProfileEvent G a b ell then (1 : Real) else 0) =
      (1 / (2 : Real) ^ (G.card + 1)) * G.powerset.sum (fun C =>
        nativeVanishingProfileCoefficient C a *
          ((numeratorKernel (nativeSignedRowProduct C C) ell).re +
            nativeWordSign b * (numeratorKernel (-nativeSignedRowProduct C C) ell).re)) := by
  rw [native_phase_profile_pointwise_selector P hP G hG a b ell hell hell2 hlarge,
    native_paired_profile_full_mask_expansion, pow_succ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  have hodd := hell.odd_of_ne_two (by omega)
  have h0 : (numeratorKernel (nativeSignedRowProduct C C) ell).re =
      C.prod (fun e => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) *
        C.prod (fun e => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re) := by
    rw [nativeSignedRowProduct, real_kernel_mul,
      real_kernel_finset_product C nativeSignedLowerCoefficient ell hodd,
      real_kernel_finset_product C nativeSignedUpperCoefficient ell hodd]
  have h1 : (numeratorKernel (-nativeSignedRowProduct C C) ell).re =
      nativeQuadraticPhase ell *
        (C.prod (fun e => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) *
          C.prod (fun e => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re)) := by
    have hn : -nativeSignedRowProduct C C = (-1 : Int) * nativeSignedRowProduct C C := by ring
    rw [hn, real_kernel_mul, h0]
    rfl
  rw [h0, h1]
  unfold nativeWordBit nativeVanishingProfileCoefficient
  have h2 : Not ((2 : Real) ^ G.card = 0) := pow_ne_zero _ (by norm_num)
  field_simp [h2]

theorem native_phase_profile_mass_expansion (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) (Y X : Nat) (hY : 2 < Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativePhaseProfileMass G a b Y X =
      (1 / (2 : Real) ^ (G.card + 1)) * G.powerset.sum (fun C =>
        nativeVanishingProfileCoefficient C a *
          (primeCorrelation (nativeSignedRowProduct C C) Y X +
            nativeWordSign b * primeCorrelation (-nativeSignedRowProduct C C) Y X)) := by
  let Q := (Finset.Ico Y X).filter Nat.Prime
  let K : Real := 1 / (2 : Real) ^ (G.card + 1)
  have hpoint : forall ell : Nat, Membership.mem Q ell ->
      (1 / (ell : Real)) * (if nativePhaseProfileEvent G a b ell then 1 else 0) =
        K * G.powerset.sum (fun C => nativeVanishingProfileCoefficient C a *
          ((1 / (ell : Real)) *
            ((numeratorKernel (nativeSignedRowProduct C C) ell).re +
              nativeWordSign b * (numeratorKernel (-nativeSignedRowProduct C C) ell).re))) := by
    intro ell hell
    have hh := Finset.mem_filter.mp hell
    have hb := Finset.mem_Ico.mp hh.1
    have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
      fun p hp => (hPY p hp).trans_le hb.1
    rw [native_phase_profile_pointwise_expansion P hP G hG a b ell hh.2 (by omega) hlarge]
    dsimp only [K]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  unfold nativePhaseProfileMass
  change Q.sum (fun ell => (1 / (ell : Real)) *
    (if nativePhaseProfileEvent G a b ell then 1 else 0)) = _
  rw [Finset.sum_congr rfl hpoint, <- Finset.mul_sum]
  change K * _ = K * _
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [<- Finset.mul_sum]
  change _ = nativeVanishingProfileCoefficient C a *
    (Q.sum (fun ell => (1 / (ell : Real)) *
        (numeratorKernel (nativeSignedRowProduct C C) ell).re) +
      nativeWordSign b * Q.sum (fun ell => (1 / (ell : Real)) *
        (numeratorKernel (-nativeSignedRowProduct C C) ell).re))
  congr 1
  rw [Finset.mul_sum, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem native_phase_profile_mass_expansion_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    Filter.Eventually (fun U : Nat =>
      nativePhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) =
      (1 / (2 : Real) ^ (G.card + 1)) * G.powerset.sum (fun C =>
        nativeVanishingProfileCoefficient C a *
          (primeCorrelation (nativeSignedRowProduct C C) (preciseCore U + 1)
              (preciseCore U * preciseCore U + 1) +
            nativeWordSign b * primeCorrelation (-nativeSignedRowProduct C C)
              (preciseCore U + 1) (preciseCore U * preciseCore U + 1)))) atTop := by
  filter_upwards [native_graph_field_window_eventually P] with U hU
  exact native_phase_profile_mass_expansion P hP G hG a b _ _ hU.1 hU.2

theorem native_phase_band_expansion (b : Bool) (Y X : Nat) (hY : 2 < Y) :
    nativePhaseBand b Y X =
      (1 / 2 : Real) * reciprocalBand Y X +
        (nativeWordSign b / 2) * primeCorrelation (-1) Y X := by
  unfold nativePhaseBand reciprocalBand primeCorrelation
  rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hb := Finset.mem_Ico.mp hh.1
  have hs := native_quadratic_phase_square_one ell hh.2 (by omega)
  have hbit : (if nativeQuadraticPhaseEvent b ell then (1 : Real) else 0) =
      nativeWordBit b (nativeQuadraticPhase ell) := by
    rw [native_word_bit_eq_indicator b (nativeQuadraticPhase ell) hs]
    by_cases hp : nativeQuadraticPhaseEvent b ell
    . have he : nativeQuadraticPhase ell = nativeWordSign b := hp
      rw [ite_eq_left hp, ite_eq_left he]
    . have he : Not (nativeQuadraticPhase ell = nativeWordSign b) := hp
      rw [ite_eq_right hp, ite_eq_right he]
  rw [hbit]
  unfold nativeWordBit nativeQuadraticPhase
  ring

theorem native_phase_incompatible_mass_zero (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) (hn : Not (nativePhaseProfileCompatible P G a b))
    (Y X : Nat) (hY : 2 < Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativePhaseProfileMass G a b Y X = 0 := by
  unfold nativePhaseProfileMass
  apply Finset.sum_eq_zero
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hb := Finset.mem_Ico.mp hh.1
  have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
    fun p hp => (hPY p hp).trans_le hb.1
  have he : Not (nativePhaseProfileEvent G a b ell) :=
    fun h => hn (native_phase_profile_event_compatible P hP G hG a b ell hh.2
      (by omega) hlarge h)
  rw [ite_eq_right he, mul_zero]

theorem native_phase_incompatible_mass_zero_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) (hn : Not (nativePhaseProfileCompatible P G a b)) :
    Filter.Eventually (fun U : Nat =>
      nativePhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) = 0) atTop := by
  filter_upwards [native_graph_field_window_eventually P] with U hU
  exact native_phase_incompatible_mass_zero P hP G hG a b hn _ _ hU.1 hU.2

end PrimeFactorOscillations.FiniteFieldIntegerSignature
