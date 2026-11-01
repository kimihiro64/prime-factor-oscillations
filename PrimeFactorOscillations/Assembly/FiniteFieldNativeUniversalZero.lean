/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeGraphOutputs
import PrimeFactorOscillations.Helpers.NativePrimeDiagonalCycles

/-! # Universal simultaneous central-output frequency

The zero-trace atom is determined by the finite prime-vertex graph for
arbitrary actual prime labels. Gap arithmetic can change the nonzero
constant-trace terms, but not this central atom.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

theorem native_graph_diagonal_indicator_zero_outside_cycles (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G C : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hCG : C <= G) (hn : Not (Membership.mem (nativeEvenCycleMasks P G) C)) :
    numeratorPrincipalIndicator (nativeSignedRowProduct C C) = 0 := by
  have hnsq : Not (IsSquare (nativeSignedRowProduct C C)) := by
    intro hsq
    have hd := (native_signed_diagonal_isSquare_iff P hP C (hCG.trans hG)).mp hsq
    exact hn ((native_even_cycle_masks_mem_iff P G C).mpr (And.intro hCG hd))
  rw [numerator_principal_indicator_int_eq_square _
    (native_signed_row_product_ne_zero P hP C C (hCG.trans hG) (hCG.trans hG)),
    ite_eq_right hnsq]

theorem native_graph_zero_rate_eq_universal (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    nativeGraphZeroTraceRate G =
      (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real) := by
  let f := fun C : Finset (Prod Nat Nat) => (-1 : Real) ^ C.card *
    numeratorPrincipalIndicator (nativeSignedRowProduct C C)
  have hsub : nativeEvenCycleMasks P G <= G.powerset := Finset.filter_subset _ _
  have ho : forall C : Finset (Prod Nat Nat), Membership.mem G.powerset C ->
      Not (Membership.mem (nativeEvenCycleMasks P G) C) -> f C = 0 := by
    intro C hC hn
    change (-1 : Real) ^ C.card *
      numeratorPrincipalIndicator (nativeSignedRowProduct C C) = 0
    rw [native_graph_diagonal_indicator_zero_outside_cycles P hP G C hG
      (Finset.mem_powerset.mp hC) hn, mul_zero]
  have hm : (nativeEvenCycleMasks P G).sum f = (nativeEvenCycleCount P G : Real) := by
    calc
      _ = (nativeEvenCycleMasks P G).sum (fun _ => (1 : Real)) := by
        apply Finset.sum_congr rfl
        intro C hC
        exact native_graph_zero_mask_eq_one_of_cycle P hP G hG C hC
      _ = _ := by simp [nativeEvenCycleCount]
  have hall : G.powerset.sum f = (nativeEvenCycleCount P G : Real) :=
    (Finset.sum_subset hsub ho).symm.trans hm
  change (1 / (2 : Real) ^ G.card) * G.powerset.sum f =
    (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real)
  rw [hall]

theorem native_graph_zero_universal_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    Tendsto (fun U : Nat =>
      nativeGraphZeroTraceMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds ((1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real))) := by
  rw [<- native_graph_zero_rate_eq_universal P hP G hG]
  exact native_graph_zero_ratio_tendsto P hP G hG

theorem native_graph_agreement_central_decomposition (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    nativeGraphAgreementRate G =
      (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real) +
        nativeSignedGeneralWordRate G G (fun _ => true) (fun _ => true) +
        nativeSignedGeneralWordRate G G (fun _ => false) (fun _ => false) := by
  unfold nativeGraphAgreementRate
  rw [native_graph_zero_rate_eq_universal P hP G hG]

def nativeGraphCentralWeightEvent (G : Finset (Prod Nat Nat)) (ell : Nat) : Prop :=
  forall e : Prod Nat Nat, Membership.mem G e ->
    integerNativeWeight e.1 (e.2 - e.1) ell =
      ((ell : Real) - 1) / ((ell : Real) - 3)

def nativeGraphCentralWeightMass (G : Finset (Prod Nat Nat)) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if nativeGraphCentralWeightEvent G ell then 1 else 0))

theorem native_graph_central_weight_iff_zero (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    nativeGraphCentralWeightEvent G ell <-> nativeGraphZeroTraceEvent G ell := by
  let : Fact (Nat.Prime ell) := Fact.mk hell
  have hR : (5 : Real) <= (ell : Real) := by exact_mod_cast hell5
  have hNZ : Not ((ell : Real) - 3 = 0) := by linarith only [hR]
  have ha : forall e : Prod Nat Nat, Membership.mem G e ->
      ((ell : Real) - 3) * integerNativeWeight e.1 (e.2 - e.1) ell -
        ((ell : Real) - 1) = nativeTrace e.1 (e.2 - e.1) ell := by
    intro e he
    have hm := (native_gap_edges_mem_iff P e).mp (hG he)
    apply native_weight_large_prime_trace e.1 (e.2 - e.1) ell
      (hP e.1 hm.1).pos hell5
    rw [Nat.add_sub_of_le hm.2.2.le]
    exact hlarge e.2 hm.2.1
  constructor
  . intro hw e he
    have hlin := ha e he
    have hdiv := (div_eq_iff hNZ).mp (hw e he).symm
    nlinarith only [hlin, hdiv]
  . intro hz e he
    have hlin := ha e he
    have ht := hz e he
    have hdiv : ((ell : Real) - 1) / ((ell : Real) - 3) =
        integerNativeWeight e.1 (e.2 - e.1) ell :=
      (div_eq_iff hNZ).mpr (by nlinarith only [hlin, ht])
    exact hdiv.symm

theorem native_graph_central_weight_mass_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (Y X : Nat) (hY : 5 <= Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeGraphCentralWeightMass G Y X = nativeGraphZeroTraceMass G Y X := by
  unfold nativeGraphCentralWeightMass nativeGraphZeroTraceMass
  apply Finset.sum_congr rfl
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hb := Finset.mem_Ico.mp hh.1
  have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
    fun p hp => (hPY p hp).trans_le hb.1
  have hi := native_graph_central_weight_iff_zero P hP G hG ell hh.2 (hY.trans hb.1) hlarge
  by_cases h : nativeGraphCentralWeightEvent G ell
  . rw [ite_eq_left h, ite_eq_left (hi.mp h)]
  . have hn : Not (nativeGraphZeroTraceEvent G ell) := fun ht => h (hi.mpr ht)
    rw [ite_eq_right h, ite_eq_right hn]

theorem native_graph_central_weight_mass_eq_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    Filter.Eventually (fun U : Nat =>
      nativeGraphCentralWeightMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) =
      nativeGraphZeroTraceMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)) atTop := by
  filter_upwards [native_graph_field_window_eventually P,
    precise_core_tendsto_atTop.eventually_ge_atTop 4] with U hU h4
  exact native_graph_central_weight_mass_eq P hP G hG _ _ (by omega) hU.2

theorem native_graph_central_weight_universal_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    Tendsto (fun U : Nat =>
      nativeGraphCentralWeightMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds ((1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real))) := by
  apply (native_graph_zero_universal_ratio_tendsto P hP G hG).congr'
  filter_upwards [native_graph_central_weight_mass_eq_eventually P hP G hG] with U hU
  rw [hU]

theorem native_graph_small_central_weight_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card <= 3) :
    Tendsto (fun U : Nat =>
      nativeGraphCentralWeightMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / (2 : Real) ^ G.card)) := by
  have h := native_graph_central_weight_universal_ratio_tendsto P hP G hG
  rw [native_even_cycle_count_small P G hG hc, Nat.cast_one, mul_one] at h
  exact h

theorem native_graph_four_cycle_central_weight_ratio_tendsto (P : Finset Nat)
    (hP : forall x : Nat, Membership.mem P x -> Nat.Prime x)
    (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    Tendsto (fun U : Nat =>
      nativeGraphCentralWeightMass (nativePrimeFourCycle p q r s)
        (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / 8 : Real)) := by
  have h := native_graph_central_weight_universal_ratio_tendsto P hP _
    (native_four_cycle_support P p q r s hp hq hr hs hpq hqr hrs)
  rw [native_even_cycle_count_four_cycle P p q r s hp hq hr hs hpq hqr hrs,
    native_four_cycle_card p q r s hpq hqr hrs] at h
  norm_num at h
  exact h

end PrimeFactorOscillations.FiniteFieldIntegerSignature
