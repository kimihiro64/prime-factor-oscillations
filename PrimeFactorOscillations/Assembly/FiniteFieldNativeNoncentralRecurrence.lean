/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeNegativeCoincidence

/-! # Arithmetic rigidity and actual noncentral agreement recurrence -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerCharacter
open FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeGraphNoncentralAgreementEvent (G : Finset (Prod Nat Nat)) (ell : Nat) : Prop :=
  And (nativeGraphWeightAgreementEvent G ell)
    (Not (nativeCentralProfileEvent G (fun _ => false) ell))

def nativeGraphPhaseNoncentralAgreementMass (G : Finset (Prod Nat Nat))
    (b : Bool) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) *
      (if And (nativeQuadraticPhaseEvent b ell) (nativeGraphNoncentralAgreementEvent G ell)
        then 1 else 0))

theorem native_negative_square_real_kernel_nonpos (k : Int) (ell : Nat)
    (hphase : nativeQuadraticPhaseEvent false ell) :
    (numeratorKernel (-(k * k)) ell).re <= 0 := by
  have hp : (numeratorKernel (-1) ell).re = -1 := hphase
  have he : -(k * k) = (-1 : Int) * (k * k) := by ring
  rw [he, real_kernel_mul, real_kernel_mul, hp]
  nlinarith [sq_nonneg ((numeratorKernel k ell).re)]

theorem native_synchronized_word_even_row_product
    (G O T : Finset (Prod Nat Nat)) (hO : O <= G) (hT : T <= G)
    (heven : (O.card + T.card) % 2 = 0) (ell : Nat) (hodd : Odd ell)
    (b : Bool) (hw : nativeSignedWordEvent G G (fun _ => b) (fun _ => b) ell) :
    (numeratorKernel (nativeSignedRowProduct O T) ell).re = 1 := by
  have hL : O.prod (fun e => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) =
      nativeWordSign b ^ O.card := by
    calc
      _ = O.prod (fun _ => nativeWordSign b) := by
        apply Finset.prod_congr rfl
        intro e he
        exact hw.1 e (hO he)
      _ = _ := by simp
  have hR : T.prod (fun e => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re) =
      nativeWordSign b ^ T.card := by
    calc
      _ = T.prod (fun _ => nativeWordSign b) := by
        apply Finset.prod_congr rfl
        intro e he
        exact hw.2 e (hT he)
      _ = _ := by simp
  have hn : O.card + T.card = 2 * ((O.card + T.card) / 2) := by omega
  rw [nativeSignedRowProduct, real_kernel_mul,
    real_kernel_finset_product O nativeSignedLowerCoefficient ell hodd,
    real_kernel_finset_product T nativeSignedUpperCoefficient ell hodd,
    hL, hR, <- pow_add, hn, pow_mul, native_word_sign_square, one_pow]

theorem native_square_row_obstruction_signed_word_impossible
    (G : Finset (Prod Nat Nat)) (ho : nativeOddSquareRowObstruction G)
    (ell : Nat) (hodd : Odd ell) (hphase : nativeQuadraticPhaseEvent false ell) (b : Bool) :
    Not (nativeSignedWordEvent G G (fun _ => b) (fun _ => b) ell) := by
  intro hw
  choose w hwrow using ho
  have hr := (native_even_square_row_pairs_mem_iff G w).mp hwrow.1
  choose k hk using hr.2.2.2
  have hn : w.1.card = 2 * (w.1.card / 2) + 1 := by omega
  have hp : (-1 : Int) ^ w.1.card = -1 := by
    rw [hn, pow_add, pow_mul]
    norm_num
  have hf : nativeSignedRowProduct w.1 w.2 = -((k : Int) * (k : Int)) := by
    rw [native_signed_row_product_factorization]
    change (-1 : Int) ^ w.1.card * (nativeUnsignedRowProduct w.1 w.2 : Int) =
      -((k : Int) * (k : Int))
    rw [hp, hk]
    push_cast
    ring
  have hv := native_synchronized_word_even_row_product G w.1 w.2 hr.1 hr.2.1
    hr.2.2.1 ell hodd b hw
  rw [hf] at hv
  have hnp := native_negative_square_real_kernel_nonpos (k : Int) ell hphase
  linarith only [hv, hnp]

theorem native_arithmetic_obstruction_agreement_iff_zero (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty)
    (ho : nativeOddSquareRowObstruction G) (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hphase : nativeQuadraticPhaseEvent false ell) :
    nativeGraphAgreementEvent G ell <-> nativeGraphZeroTraceEvent G ell := by
  have hodd : Odd ell := hell.odd_of_ne_two (by omega)
  have hp := native_square_row_obstruction_signed_word_impossible G ho ell hodd hphase true
  have hm := native_square_row_obstruction_signed_word_impossible G ho ell hodd hphase false
  have hd := native_graph_agreement_pointwise_decomposition P hP G hG hne ell hell hell2 hlarge
  rw [ite_eq_right hp, ite_eq_right hm, add_zero, add_zero] at hd
  constructor
  . intro ha
    by_contra hz
    rw [ite_eq_left ha, ite_eq_right hz] at hd
    norm_num at hd
  . intro hz e he f hf
    exact (hz e he).trans (hz f hf).symm

theorem native_arithmetic_obstruction_weight_rigidity (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty)
    (ho : nativeOddSquareRowObstruction G) (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hphase : nativeQuadraticPhaseEvent false ell) :
    nativeGraphWeightAgreementEvent G ell <->
      nativeCentralProfileEvent G (fun _ => false) ell := by
  have hw := native_graph_weight_agreement_iff P hP G hG ell hell hell5 hlarge
  have ht := native_arithmetic_obstruction_agreement_iff_zero P hP G hG hne ho ell hell
    (by omega) hlarge hphase
  have hc := native_central_profile_iff_vanishing P hP G hG (fun _ => false)
    ell hell hell5 hlarge
  constructor
  . intro h
    exact hc.mpr (ht.mp (hw.mp h))
  . intro h
    exact hw.mpr (ht.mpr (hc.mp h))

theorem native_arithmetic_obstruction_mod_four_rigidity (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty)
    (ho : nativeOddSquareRowObstruction G) (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) (hmod : ell % 4 = 3) :
    nativeGraphWeightAgreementEvent G ell <->
      nativeCentralProfileEvent G (fun _ => false) ell := by
  apply native_arithmetic_obstruction_weight_rigidity P hP G hG hne ho ell hell hell5 hlarge
  exact (native_phase_event_mod_four false ell hell (by omega)).mpr hmod

theorem native_central_profile_weight_agreement (G : Finset (Prod Nat Nat)) (ell : Nat)
    (hc : nativeCentralProfileEvent G (fun _ => false) ell) :
    nativeGraphWeightAgreementEvent G ell := by
  intro e he f hf
  exact (hc e he).trans (hc f hf).symm

theorem native_noncentral_agreement_all_off_center (G : Finset (Prod Nat Nat)) (ell : Nat)
    (hn : nativeGraphNoncentralAgreementEvent G ell) :
    nativeCentralProfileEvent G (fun _ => true) ell := by
  intro e he
  change Not (integerNativeWeight e.1 (e.2 - e.1) ell =
    ((ell : Real) - 1) / ((ell : Real) - 3))
  intro hz
  apply hn.2
  intro f hf
  change integerNativeWeight f.1 (f.2 - f.1) ell =
    ((ell : Real) - 1) / ((ell : Real) - 3)
  exact (hn.1 f hf e he).trans hz

theorem native_obstructed_noncentral_agreement_impossible (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty)
    (ho : nativeOddSquareRowObstruction G) (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hphase : nativeQuadraticPhaseEvent false ell) :
    Not (nativeGraphNoncentralAgreementEvent G ell) := by
  intro hn
  exact hn.2 ((native_arithmetic_obstruction_weight_rigidity P hP G hG hne ho ell hell hell5
    hlarge hphase).mp hn.1)

theorem native_graph_phase_noncentral_mass_partition
    (G : Finset (Prod Nat Nat)) (b : Bool) (Y X : Nat) :
    nativeGraphPhaseWeightAgreementMass G b Y X =
      nativeCentralPhaseProfileMass G (fun _ => false) b Y X +
        nativeGraphPhaseNoncentralAgreementMass G b Y X := by
  unfold nativeGraphPhaseWeightAgreementMass nativeCentralPhaseProfileMass
    nativeGraphPhaseNoncentralAgreementMass nativeCentralPhaseProfileEvent
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell hell
  by_cases hp : nativeQuadraticPhaseEvent b ell
  . by_cases hc : nativeCentralProfileEvent G (fun _ => false) ell
    . have ha := native_central_profile_weight_agreement G ell hc
      simp [nativeGraphNoncentralAgreementEvent, hp, hc, ha]
    . by_cases ha : nativeGraphWeightAgreementEvent G ell <;>
        simp [nativeGraphNoncentralAgreementEvent, hp, hc, ha]
  . simp [hp]


theorem native_graph_negative_phase_noncentral_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseNoncentralAgreementMass G false (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand false (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if nativeOddSquareRowObstruction G then 0 else
        (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEvenSquareRowCount G : Real)))) := by
  let C : Real := (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real)
  let T : Real := if nativeOddSquareRowObstruction G then 0 else
    (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEvenSquareRowCount G : Real))
  have ha : Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G false (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand false (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (C + T)) :=
    native_graph_negative_phase_weight_dichotomy_ratio_tendsto P hP G hG hne
  have hc : Tendsto (fun U : Nat =>
      nativeCentralPhaseProfileMass G (fun _ => false) false (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand false (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds C) := by
    have h := native_central_profile_mod_four_ratio_tendsto P hP G hG (fun _ => false) false
    rw [ite_eq_left (native_central_negative_phase_compatible P G)] at h
    exact h
  have hl := ha.sub hc
  have he : (C + T) - C = T := by ring
  rw [he] at hl
  apply hl.congr'
  filter_upwards [] with U
  rw [native_graph_phase_noncentral_mass_partition]
  ring

theorem native_noncentral_negative_realization_above (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty)
    (hno : Not (nativeOddSquareRowObstruction G)) (B : Nat) :
    Exists (fun ell : Nat => And (Nat.Prime ell)
      (And (B < ell) (And (ell % 4 = 3) (nativeGraphNoncentralAgreementEvent G ell)))) := by
  have hlim := native_graph_negative_phase_noncentral_ratio_tendsto P hP G hG hne
  rw [ite_eq_right hno] at hlim
  have hK : 0 < (nativeEvenSquareRowCount G : Real) := by
    exact_mod_cast native_even_square_row_count_positive G
  have hr : 0 < (1 / (2 : Real) ^ (G.card + G.card)) *
      (2 * (nativeEvenSquareRowCount G : Real)) := by positivity
  have hp := hlim.eventually (Ioi_mem_nhds hr)
  have htail := precise_core_tendsto_atTop.eventually_ge_atTop (max (B + 1) 5)
  choose U hU using (hp.and htail).exists
  have hbcore : B + 1 <= preciseCore U := (Nat.le_max_left (B + 1) 5).trans hU.2
  have h5core : 5 <= preciseCore U := (Nat.le_max_right (B + 1) 5).trans hU.2
  by_contra hn
  have hz : nativeGraphPhaseNoncentralAgreementMass G false (preciseCore U + 1)
      (preciseCore U * preciseCore U + 1) = 0 := by
    unfold nativeGraphPhaseNoncentralAgreementMass
    apply Finset.sum_eq_zero
    intro ell hell
    have hh := Finset.mem_filter.mp hell
    have hb := Finset.mem_Ico.mp hh.1
    have hnell : Not (And (nativeQuadraticPhaseEvent false ell)
        (nativeGraphNoncentralAgreementEvent G ell)) := by
      intro he
      have hmod : ell % 4 = 3 :=
        (native_phase_event_mod_four false ell hh.2 (by omega)).mp he.1
      exact hn (Exists.intro ell (And.intro hh.2
        (And.intro (by omega) (And.intro hmod he.2))))
    rw [ite_eq_right hnell, mul_zero]
  have hpos := hU.1
  rw [hz, zero_div] at hpos
  exact (lt_irrefl (0 : Real)) hpos

theorem native_noncentral_negative_recurrence_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty) :
    (forall B : Nat, Exists (fun ell : Nat => And (Nat.Prime ell)
      (And (B < ell) (And (ell % 4 = 3) (nativeGraphNoncentralAgreementEvent G ell))))) <->
      Not (nativeOddSquareRowObstruction G) := by
  constructor
  . intro hrec ho
    choose K hK using P.finite_toSet.bddAbove
    choose ell hell using hrec (max K 5)
    have hKell : K < ell := lt_of_le_of_lt (Nat.le_max_left K 5) hell.2.1
    have h5ell : 5 < ell := lt_of_le_of_lt (Nat.le_max_right K 5) hell.2.1
    have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
      fun p hp => lt_of_le_of_lt (hK hp) hKell
    have hphase : nativeQuadraticPhaseEvent false ell :=
      (native_phase_event_mod_four false ell hell.1 (by omega)).mpr hell.2.2.1
    exact native_obstructed_noncentral_agreement_impossible P hP G hG hne ho ell hell.1
      (by omega) hlarge hphase hell.2.2.2
  . intro hno B
    exact native_noncentral_negative_realization_above P hP G hG hne hno B

theorem native_arithmetic_obstruction_iff_eventual_rigidity (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty) :
    nativeOddSquareRowObstruction G <->
      Exists (fun B : Nat => forall ell : Nat, Nat.Prime ell -> B < ell -> ell % 4 = 3 ->
        (nativeGraphWeightAgreementEvent G ell <->
          nativeCentralProfileEvent G (fun _ => false) ell)) := by
  constructor
  . intro ho
    choose K hK using P.finite_toSet.bddAbove
    refine Exists.intro (max K 5) ?_
    intro ell hell hB hmod
    have hKell : K < ell := lt_of_le_of_lt (Nat.le_max_left K 5) hB
    have h5ell : 5 < ell := lt_of_le_of_lt (Nat.le_max_right K 5) hB
    apply native_arithmetic_obstruction_mod_four_rigidity P hP G hG hne ho ell hell
      (by omega) _ hmod
    intro p hp
    exact lt_of_le_of_lt (hK hp) hKell
  . intro hev
    by_contra hno
    choose B hB using hev
    choose ell hell using native_noncentral_negative_realization_above P hP G hG hne hno B
    have hc := (hB ell hell.1 hell.2.1 hell.2.2.1).mp hell.2.2.2.1
    exact hell.2.2.2.2 hc
end PrimeFactorOscillations.FiniteFieldIntegerSignature
