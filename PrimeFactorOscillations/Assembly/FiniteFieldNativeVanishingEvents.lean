/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeUniversalZero
import PrimeFactorOscillations.Helpers.NativeVanishingProfileAlgebra

/-! # Actual native vanishing profiles and exact cycle constraints

True denotes a nonzero trace; false denotes a zero trace. All finite
supports and profiles are fixed before the independent field-prime limit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeVanishingProfileEvent (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (ell : Nat) : Prop :=
  forall e : Prod Nat Nat, Membership.mem G e ->
    if a e then Not (nativeTrace e.1 (e.2 - e.1) ell = 0)
      else nativeTrace e.1 (e.2 - e.1) ell = 0

def nativeVanishingProfileMass (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if nativeVanishingProfileEvent G a ell then 1 else 0))

def nativeVanishingProfileCoefficient (C : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) : Real :=
  C.prod (fun e => nativeWordSign (a e))

def nativeVanishingProfileCompatible (P : Finset Nat) (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) : Prop :=
  forall C : Finset (Prod Nat Nat), Membership.mem (nativeEvenCycleMasks P G) C ->
    nativeVanishingProfileCoefficient C a = 1

def nativeVanishingProfileRate (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) : Real :=
  (1 / (2 : Real) ^ G.card) * G.powerset.sum (fun C =>
    nativeVanishingProfileCoefficient C a *
      numeratorPrincipalIndicator (nativeSignedRowProduct C C))

theorem native_cycle_paired_character_product_one (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hcard : C.card % 2 = 0) (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    C.prod (fun e =>
      (numeratorKernel (nativeSignedLowerCoefficient e) ell).re *
        (numeratorKernel (nativeSignedUpperCoefficient e) ell).re) = 1 := by
  let x := fun e : Prod Nat Nat => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re
  let y := fun e : Prod Nat Nat => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re
  have hx : (C.prod x) ^ 2 = 1 := by
    rw [<- Finset.prod_pow]
    calc
      _ = C.prod (fun _ => (1 : Real)) := by
        apply Finset.prod_congr rfl
        intro e he
        exact (native_signed_edge_kernel_squares P hP e (hC he) ell hell hell2 hlarge).1
      _ = 1 := by simp
  have hy : (C.prod y) ^ 2 = 1 := by
    rw [<- Finset.prod_pow]
    calc
      _ = C.prod (fun _ => (1 : Real)) := by
        apply Finset.prod_congr rfl
        intro e he
        exact (native_signed_edge_kernel_squares P hP e (hC he) ell hell hell2 hlarge).2
      _ = 1 := by simp
  have hr : (C.prod x * C.prod y) ^ 2 = 1 := by rw [mul_pow, hx, hy]; norm_num
  have hodd := hell.odd_of_ne_two (by omega)
  have hid : C.prod x * C.prod y =
      (numeratorKernel (nativeSignedRowProduct C C) ell).re := by
    rw [nativeSignedRowProduct, real_kernel_mul,
      real_kernel_finset_product C nativeSignedLowerCoefficient ell hodd,
      real_kernel_finset_product C nativeSignedUpperCoefficient ell hodd]
  choose k hk using native_signed_cycle_product_isSquare P C hC hdeg hcard
  have hn : 0 <= C.prod x * C.prod y := by
    rw [hid, hk, real_kernel_mul]
    exact mul_self_nonneg _
  have hz : (C.prod x * C.prod y - 1) * (C.prod x * C.prod y + 1) = 0 := by
    nlinarith only [hr]
  have hone : C.prod x * C.prod y = 1 := by
    rcases mul_eq_zero.mp hz with h | h
    . exact sub_eq_zero.mp h
    . linarith only [h, hn]
  simpa only [x, y, Finset.prod_mul_distrib] using hone

theorem native_vanishing_profile_event_compatible (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hevent : nativeVanishingProfileEvent G a ell) :
    nativeVanishingProfileCompatible P G a := by
  intro C hC
  have hc := (native_even_cycle_masks_mem_iff P G C).mp hC
  have hsign : forall e : Prod Nat Nat, Membership.mem C e ->
      (numeratorKernel (nativeSignedLowerCoefficient e) ell).re *
        (numeratorKernel (nativeSignedUpperCoefficient e) ell).re = nativeWordSign (a e) := by
    intro e he
    have hg := hc.1 he
    have hu := native_signed_edge_kernel_squares P hP e (hG hg) ell hell hell2 hlarge
    have ht := native_trace_eq_signed_rows e.1 e.2 ell
      ((native_gap_edges_mem_iff P e).mp (hG hg)).2.2
    have hs := hevent e hg
    rw [ht] at hs
    exact (native_trace_status_iff_paired_sign (a e) _ _ hu.1 hu.2).mp hs
  unfold nativeVanishingProfileCoefficient
  rw [<- Finset.prod_congr rfl hsign]
  exact native_cycle_paired_character_product_one P hP C (hc.1.trans hG)
    hc.2.1 hc.2.2 ell hell hell2 hlarge

theorem native_vanishing_profile_pointwise_selector (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    (if nativeVanishingProfileEvent G a ell then (1 : Real) else 0) =
      G.prod (fun e => nativeWordBit (a e)
        ((numeratorKernel (nativeSignedLowerCoefficient e) ell).re *
          (numeratorKernel (nativeSignedUpperCoefficient e) ell).re)) := by
  let x := fun e : Prod Nat Nat => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re
  let y := fun e : Prod Nat Nat => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re
  have hx : forall e : Prod Nat Nat, Membership.mem G e -> x e ^ 2 = 1 :=
    fun e he => (native_signed_edge_kernel_squares P hP e (hG he) ell hell hell2 hlarge).1
  have hy : forall e : Prod Nat Nat, Membership.mem G e -> y e ^ 2 = 1 :=
    fun e he => (native_signed_edge_kernel_squares P hP e (hG he) ell hell hell2 hlarge).2
  have ht : forall e : Prod Nat Nat, Membership.mem G e ->
      nativeTrace e.1 (e.2 - e.1) ell = x e + y e := by
    intro e he
    exact native_trace_eq_signed_rows e.1 e.2 ell
      ((native_gap_edges_mem_iff P e).mp (hG he)).2.2
  change (if nativeVanishingProfileEvent G a ell then (1 : Real) else 0) =
    G.prod (fun e => nativeWordBit (a e) (x e * y e))
  rw [native_paired_profile_selector G a x y hx hy]
  by_cases h : nativeVanishingProfileEvent G a ell
  . have hs : forall e : Prod Nat Nat, Membership.mem G e ->
        if a e then Not (x e + y e = 0) else x e + y e = 0 := by
      intro e he
      rw [<- ht e he]
      exact h e he
    rw [ite_eq_left h, ite_eq_left hs]
  . have hs : Not (forall e : Prod Nat Nat, Membership.mem G e ->
        if a e then Not (x e + y e = 0) else x e + y e = 0) := by
      intro hxy
      apply h
      intro e he
      rw [ht e he]
      exact hxy e he
    rw [ite_eq_right h, ite_eq_right hs]

theorem native_vanishing_profile_mass_expansion (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (Y X : Nat) (hY : 2 < Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeVanishingProfileMass G a Y X =
      (1 / (2 : Real) ^ G.card) * G.powerset.sum (fun C =>
        nativeVanishingProfileCoefficient C a * nativeSignedRowMoment C C Y X) := by
  let Q := (Finset.Ico Y X).filter Nat.Prime
  let K : Real := 1 / (2 : Real) ^ G.card
  have hpoint : forall ell : Nat, Membership.mem Q ell ->
      (1 / (ell : Real)) * (if nativeVanishingProfileEvent G a ell then 1 else 0) =
        K * G.powerset.sum (fun C => nativeVanishingProfileCoefficient C a *
          ((1 / (ell : Real)) *
            (C.prod (fun e => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) *
              C.prod (fun e => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re)))) := by
    intro ell hell
    have hh := Finset.mem_filter.mp hell
    have hb := Finset.mem_Ico.mp hh.1
    have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
      fun p hp => (hPY p hp).trans_le hb.1
    rw [native_vanishing_profile_pointwise_selector P hP G hG a ell hh.2 (by omega) hlarge,
      native_paired_profile_full_mask_expansion]
    dsimp only [K, nativeVanishingProfileCoefficient]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  unfold nativeVanishingProfileMass
  change Q.sum (fun ell => (1 / (ell : Real)) *
    (if nativeVanishingProfileEvent G a ell then 1 else 0)) = _
  rw [Finset.sum_congr rfl hpoint, <- Finset.mul_sum]
  change K * _ = K * _
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [<- Finset.mul_sum]
  rfl

theorem native_vanishing_profile_mass_expansion_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) :
    Filter.Eventually (fun U : Nat =>
      nativeVanishingProfileMass G a (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) =
      (1 / (2 : Real) ^ G.card) * G.powerset.sum (fun C =>
        nativeVanishingProfileCoefficient C a *
          nativeSignedRowMoment C C (preciseCore U + 1)
            (preciseCore U * preciseCore U + 1))) atTop := by
  filter_upwards [native_graph_field_window_eventually P] with U hU
  exact native_vanishing_profile_mass_expansion P hP G hG a _ _ hU.1 hU.2

theorem native_vanishing_incompatible_mass_zero (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (hn : Not (nativeVanishingProfileCompatible P G a))
    (Y X : Nat) (hY : 2 < Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeVanishingProfileMass G a Y X = 0 := by
  unfold nativeVanishingProfileMass
  apply Finset.sum_eq_zero
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hb := Finset.mem_Ico.mp hh.1
  have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
    fun p hp => (hPY p hp).trans_le hb.1
  have he : Not (nativeVanishingProfileEvent G a ell) :=
    fun h => hn (native_vanishing_profile_event_compatible P hP G hG a ell hh.2
      (by omega) hlarge h)
  rw [ite_eq_right he, mul_zero]

theorem native_vanishing_incompatible_mass_zero_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (hn : Not (nativeVanishingProfileCompatible P G a)) :
    Filter.Eventually (fun U : Nat =>
      nativeVanishingProfileMass G a (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) = 0) atTop := by
  filter_upwards [native_graph_field_window_eventually P] with U hU
  exact native_vanishing_incompatible_mass_zero P hP G hG a hn _ _ hU.1 hU.2

theorem native_vanishing_profile_general_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) :
    Tendsto (fun U : Nat =>
      nativeVanishingProfileMass G a (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativeVanishingProfileRate G a)) := by
  let K : Real := 1 / (2 : Real) ^ G.card
  let F : Nat -> Real := fun U =>
    K * G.powerset.sum (fun C => nativeVanishingProfileCoefficient C a *
      (nativeSignedRowMoment C C (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1)))
  have hlim : Tendsto F atTop (nhds (nativeVanishingProfileRate G a)) := by
    dsimp only [F, K, nativeVanishingProfileRate]
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetSum G.powerset
    intro C hC
    have hsub := (Finset.mem_powerset.mp hC).trans hG
    exact Filter.Tendsto.const_mul (nativeVanishingProfileCoefficient C a)
      (native_signed_row_moment_general_ratio_tendsto C C
        (native_signed_row_product_ne_zero P hP C C hsub hsub))
  apply hlim.congr'
  filter_upwards [native_vanishing_profile_mass_expansion_eventually P hP G hG a] with U hU
  dsimp only [F, K]
  rw [hU]
  simp only [mul_div_assoc, Finset.sum_div]

end PrimeFactorOscillations.FiniteFieldIntegerSignature
