/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativePhaseWords

/-! # Sharp native coincidence with the common field phase retained -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerCharacter
open FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeGraphPhaseAgreementRate (G : Finset (Prod Nat Nat)) (b : Bool) : Real :=
  nativePhaseProfileRate G (fun _ => false) b +
    nativeSignedPhaseWordRate G G (fun _ => true) (fun _ => true) b +
    nativeSignedPhaseWordRate G G (fun _ => false) (fun _ => false) b

theorem native_graph_phase_weight_pointwise_decomposition (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) (b : Bool) (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    (if And (nativeQuadraticPhaseEvent b ell) (nativeGraphWeightAgreementEvent G ell)
      then (1 : Real) else 0) =
      (if nativeCentralPhaseProfileEvent G (fun _ => false) b ell then 1 else 0) +
        (if nativeSignedPhaseWordEvent G G (fun _ => true) (fun _ => true) b ell
          then 1 else 0) +
        (if nativeSignedPhaseWordEvent G G (fun _ => false) (fun _ => false) b ell
          then 1 else 0) := by
  by_cases hp : nativeQuadraticPhaseEvent b ell
  . simp only [nativeCentralPhaseProfileEvent, nativeSignedPhaseWordEvent, hp, true_and]
    have hz : nativeCentralProfileEvent G (fun _ => false) ell <->
        nativeGraphZeroTraceEvent G ell :=
      native_central_profile_iff_vanishing P hP G hG (fun _ => false) ell hell hell5 hlarge
    rw [native_graph_weight_agreement_iff P hP G hG ell hell hell5 hlarge, hz]
    exact native_graph_agreement_pointwise_decomposition P hP G hG hne ell hell
      (by omega) hlarge
  . simp only [nativeCentralPhaseProfileEvent, nativeSignedPhaseWordEvent, hp,
      false_and, ite_false, add_zero]

theorem native_graph_phase_weight_mass_decomposition (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) (b : Bool) (Y X : Nat) (hY : 5 <= Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeGraphPhaseWeightAgreementMass G b Y X =
      nativeCentralPhaseProfileMass G (fun _ => false) b Y X +
        nativeSignedPhaseWordMass G G (fun _ => true) (fun _ => true) b Y X +
        nativeSignedPhaseWordMass G G (fun _ => false) (fun _ => false) b Y X := by
  unfold nativeGraphPhaseWeightAgreementMass nativeCentralPhaseProfileMass nativeSignedPhaseWordMass
  rw [<- Finset.sum_add_distrib, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hb := Finset.mem_Ico.mp hh.1
  have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
    fun p hp => (hPY p hp).trans_le hb.1
  rw [native_graph_phase_weight_pointwise_decomposition P hP G hG hne b ell hh.2
    (hY.trans hb.1) hlarge]
  ring

theorem native_graph_phase_weight_mass_decomposition_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) (b : Bool) :
    Filter.Eventually (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) =
      nativeCentralPhaseProfileMass G (fun _ => false) b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) +
      nativeSignedPhaseWordMass G G (fun _ => true) (fun _ => true) b
        (preciseCore U + 1) (preciseCore U * preciseCore U + 1) +
      nativeSignedPhaseWordMass G G (fun _ => false) (fun _ => false) b
        (preciseCore U + 1) (preciseCore U * preciseCore U + 1)) atTop := by
  filter_upwards [native_graph_field_window_eventually P,
    precise_core_tendsto_atTop.eventually_ge_atTop 4] with U hU h4
  exact native_graph_phase_weight_mass_decomposition P hP G hG hne b _ _ (by omega) hU.2

theorem native_graph_phase_weight_joint_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativeGraphPhaseAgreementRate G b)) := by
  have hc := native_central_phase_profile_joint_ratio_tendsto P hP G hG (fun _ => false) b
  rw [<- native_phase_profile_rate_eq P hP G hG (fun _ => false) b] at hc
  have hp := native_signed_phase_word_joint_ratio_tendsto P hP G G hG hG
    (fun _ => true) (fun _ => true) b
  have hn := native_signed_phase_word_joint_ratio_tendsto P hP G G hG hG
    (fun _ => false) (fun _ => false) b
  apply ((hc.add hp).add hn).congr'
  filter_upwards [native_graph_phase_weight_mass_decomposition_eventually P hP G hG hne b]
    with U hU
  rw [hU]
  simp only [add_div]

theorem native_graph_phase_weight_conditional_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativePhaseBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (2 * nativeGraphPhaseAgreementRate G b)) := by
  have hj := native_graph_phase_weight_joint_ratio_tendsto P hP G hG hne b
  have hlim := hj.div (native_phase_band_ratio_tendsto b) (by norm_num)
  have hc : nativeGraphPhaseAgreementRate G b / (1 / 2 : Real) =
      2 * nativeGraphPhaseAgreementRate G b := by ring
  rw [hc] at hlim
  apply hlim.congr'
  have hm := precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive
  filter_upwards [hm, native_phase_band_eventually_positive b] with U hM hB
  have hMp : (0 : Real) <
      reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) :=
    (show (0 : Real) < Real.log 2 / 2 by positivity).trans_le hM
  simp only [Pi.div_apply]
  field_simp [ne_of_gt hMp, ne_of_gt hB]

theorem native_graph_mod_four_weight_conditional_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (2 * nativeGraphPhaseAgreementRate G b)) := by
  apply (native_graph_phase_weight_conditional_ratio_tendsto P hP G hG hne b).congr'
  filter_upwards [precise_core_tendsto_atTop.eventually_ge_atTop 3] with U hU
  rw [native_phase_band_eq_mod_four b _ _ (by omega)]

theorem native_graph_phase_constant_word_sum_expansion (G : Finset (Prod Nat Nat)) (b : Bool) :
    nativeSignedPhaseWordRate G G (fun _ => true) (fun _ => true) b +
      nativeSignedPhaseWordRate G G (fun _ => false) (fun _ => false) b =
        (1 / (2 : Real) ^ (G.card + G.card + 1)) *
          G.powerset.sum (fun O => G.powerset.sum (fun T =>
            (1 + (-1 : Real) ^ (O.card + T.card)) *
              (numeratorPrincipalIndicator (nativeSignedRowProduct O T) +
                nativeWordSign b * numeratorPrincipalIndicator (-nativeSignedRowProduct O T)))) := by
  have ht (O T : Finset (Prod Nat Nat)) :
      nativeSignedWordMaskCoefficient O T (fun _ => true) (fun _ => true) = 1 := by
    simp [nativeSignedWordMaskCoefficient, nativeWordSign]
  have hn (O T : Finset (Prod Nat Nat)) :
      nativeSignedWordMaskCoefficient O T (fun _ => false) (fun _ => false) =
        (-1 : Real) ^ (O.card + T.card) := by
    simp [nativeSignedWordMaskCoefficient, nativeWordSign, Finset.prod_const, pow_add]
  unfold nativeSignedPhaseWordRate
  simp only [ht, hn, one_mul]
  rw [<- mul_add, <- Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro O _
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  ring


def nativePositivePhaseCoincidenceFloor (P : Finset Nat) (G : Finset (Prod Nat Nat)) : Real :=
  (if nativePhaseProfileCompatible P G (fun _ => false) true then
    (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) else 0) +
  (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEulerianCount P G : Real))

theorem native_synchronized_sign_coefficient_nonneg (n : Nat) :
    0 <= 1 + (-1 : Real) ^ n := by
  have hs : ((-1 : Real) ^ n) ^ 2 = 1 := by
    rw [<- pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  nlinarith only [hs, sq_nonneg ((-1 : Real) ^ n + 1)]

theorem native_graph_positive_phase_paired_mask_nonneg (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    0 <= (1 + (-1 : Real) ^ (A.card + B.card)) *
      (numeratorPrincipalIndicator (nativeSignedRowProduct A B) +
        nativeWordSign true * numeratorPrincipalIndicator (-nativeSignedRowProduct A B)) := by
  have hD := native_signed_row_product_ne_zero P hP A B hA hB
  have hn : 0 <= numeratorPrincipalIndicator (-nativeSignedRowProduct A B) := by
    rw [numerator_principal_indicator_int_eq_square _ (neg_ne_zero.mpr hD)]
    split_ifs <;> norm_num
  have hp := native_graph_square_indicator_nonneg P hP A B hA hB
  change 0 <= (1 + (-1 : Real) ^ (A.card + B.card)) *
    (numeratorPrincipalIndicator (nativeSignedRowProduct A B) +
      (1 : Real) * numeratorPrincipalIndicator (-nativeSignedRowProduct A B))
  rw [one_mul]
  exact mul_nonneg (native_synchronized_sign_coefficient_nonneg _) (add_nonneg hp hn)

theorem native_graph_positive_phase_paired_mask_eq_two_of_eulerian (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hC : Membership.mem (nativeEulerianMasks P G) C) :
    (1 + (-1 : Real) ^ (C.card + C.card)) *
      (numeratorPrincipalIndicator (nativeSignedRowProduct C C) +
        nativeWordSign true * numeratorPrincipalIndicator (-nativeSignedRowProduct C C)) = 2 := by
  have hh := (native_eulerian_masks_mem_iff P G C).mp hC
  rw [native_phase_diagonal_indicator P hP C (hh.1.trans hG) true, ite_eq_left hh.2]
  have he : C.card + C.card = 2 * C.card := by omega
  rw [he, pow_mul]
  norm_num [nativeWordSign]

theorem native_graph_positive_phase_constant_word_rate_lower_bound (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    (1 / (2 : Real) ^ (G.card + G.card + 1)) * (2 * (nativeEulerianCount P G : Real)) <=
      nativeSignedPhaseWordRate G G (fun _ => true) (fun _ => true) true +
        nativeSignedPhaseWordRate G G (fun _ => false) (fun _ => false) true := by
  let f := fun O T : Finset (Prod Nat Nat) =>
    (1 + (-1 : Real) ^ (O.card + T.card)) *
      (numeratorPrincipalIndicator (nativeSignedRowProduct O T) +
        nativeWordSign true * numeratorPrincipalIndicator (-nativeSignedRowProduct O T))
  have hn : forall O : Finset (Prod Nat Nat), Membership.mem G.powerset O ->
      forall T : Finset (Prod Nat Nat), Membership.mem G.powerset T -> 0 <= f O T := by
    intro O hO T hT
    exact native_graph_positive_phase_paired_mask_nonneg P hP O T
      ((Finset.mem_powerset.mp hO).trans hG) ((Finset.mem_powerset.mp hT).trans hG)
  have hi : forall O : Finset (Prod Nat Nat), Membership.mem G.powerset O ->
      f O O <= G.powerset.sum (fun T => f O T) := by
    intro O hO
    exact Finset.single_le_sum (fun T hT => hn O hO T hT) hO
  have hsub : nativeEulerianMasks P G <= G.powerset := Finset.filter_subset _ _
  have hm : (nativeEulerianMasks P G).sum (fun C => f C C) =
      2 * (nativeEulerianCount P G : Real) := by
    calc
      _ = (nativeEulerianMasks P G).sum (fun _ => (2 : Real)) := by
        apply Finset.sum_congr rfl
        intro C hC
        exact native_graph_positive_phase_paired_mask_eq_two_of_eulerian P hP G hG C hC
      _ = (nativeEulerianCount P G : Real) * 2 := by simp [nativeEulerianCount]
      _ = _ := mul_comm _ _
  have hd : (nativeEulerianMasks P G).sum (fun C => f C C) <=
      G.powerset.sum (fun C => f C C) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun C hC _ => hn C hC C hC)
  rw [hm] at hd
  have hall : 2 * (nativeEulerianCount P G : Real) <=
      G.powerset.sum (fun O => G.powerset.sum (fun T => f O T)) :=
    hd.trans (Finset.sum_le_sum (fun O hO => hi O hO))
  rw [native_graph_phase_constant_word_sum_expansion]
  change (1 / (2 : Real) ^ (G.card + G.card + 1)) * (2 * (nativeEulerianCount P G : Real)) <=
    (1 / (2 : Real) ^ (G.card + G.card + 1)) *
      G.powerset.sum (fun O => G.powerset.sum (fun T => f O T))
  exact mul_le_mul_of_nonneg_left hall (by positivity)

theorem native_phase_profile_conditional_rate_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    2 * nativePhaseProfileRate G a b =
      if nativePhaseProfileCompatible P G a b then
        (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) else 0 := by
  rw [native_phase_profile_rate_eq P hP G hG a b]
  by_cases hc : nativePhaseProfileCompatible P G a b
  . rw [ite_eq_left hc, ite_eq_left hc, pow_succ]
    have h2 : Not ((2 : Real) ^ G.card = 0) := pow_ne_zero _ (by norm_num)
    field_simp [h2]
  . rw [ite_eq_right hc, ite_eq_right hc, mul_zero]

theorem native_graph_positive_phase_constant_word_conditional_lower_bound (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEulerianCount P G : Real)) <=
      2 * (nativeSignedPhaseWordRate G G (fun _ => true) (fun _ => true) true +
        nativeSignedPhaseWordRate G G (fun _ => false) (fun _ => false) true) := by
  have h := mul_le_mul_of_nonneg_left
    (native_graph_positive_phase_constant_word_rate_lower_bound P hP G hG)
    (show (0 : Real) <= 2 by norm_num)
  have heq : 2 * ((1 / (2 : Real) ^ (G.card + G.card + 1)) *
      (2 * (nativeEulerianCount P G : Real))) =
      (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEulerianCount P G : Real)) := by
    rw [pow_succ]
    have h2 : Not ((2 : Real) ^ (G.card + G.card) = 0) := pow_ne_zero _ (by norm_num)
    field_simp [h2]
  rw [heq] at h
  exact h

theorem native_graph_positive_phase_agreement_rate_lower_bound (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    nativePositivePhaseCoincidenceFloor P G <= 2 * nativeGraphPhaseAgreementRate G true := by
  have hp := native_graph_positive_phase_constant_word_conditional_lower_bound P hP G hG
  have hc := native_phase_profile_conditional_rate_eq P hP G hG (fun _ => false) true
  unfold nativePositivePhaseCoincidenceFloor
  rw [<- hc]
  unfold nativeGraphPhaseAgreementRate
  linarith only [hp]

theorem native_graph_positive_phase_weight_limit_lower_bound (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty) :
    And
      (Tendsto (fun U : Nat =>
        nativeGraphPhaseWeightAgreementMass G true (preciseCore U + 1)
          (preciseCore U * preciseCore U + 1) /
          nativeModuloFourBand true (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
        atTop (nhds (2 * nativeGraphPhaseAgreementRate G true)))
      (nativePositivePhaseCoincidenceFloor P G <= 2 * nativeGraphPhaseAgreementRate G true) :=
  And.intro (native_graph_mod_four_weight_conditional_ratio_tendsto P hP G hG hne true)
    (native_graph_positive_phase_agreement_rate_lower_bound P hP G hG)


theorem native_graph_positive_phase_constant_word_rate_eq_of_independent (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    nativeSignedPhaseWordRate G G (fun _ => true) (fun _ => true) true +
      nativeSignedPhaseWordRate G G (fun _ => false) (fun _ => false) true =
        (1 / (2 : Real) ^ (G.card + G.card + 1)) * (2 * (nativeEulerianCount P G : Real)) := by
  let f := fun O T : Finset (Prod Nat Nat) =>
    (1 + (-1 : Real) ^ (O.card + T.card)) *
      (numeratorPrincipalIndicator (nativeSignedRowProduct O T) +
        nativeWordSign true * numeratorPrincipalIndicator (-nativeSignedRowProduct O T))
  have hi : forall O : Finset (Prod Nat Nat), Membership.mem G.powerset O ->
      G.powerset.sum (fun T => f O T) = f O O := by
    intro O hO
    apply Finset.sum_eq_single O
    . intro T hT hne
      have hneq : Not (O = T) := fun h => hne h.symm
      have hz := native_phase_row_indicator_of_independent P hP hind O T
        ((Finset.mem_powerset.mp hO).trans hG) ((Finset.mem_powerset.mp hT).trans hG) true
      rw [ite_eq_right hneq] at hz
      change (1 + (-1 : Real) ^ (O.card + T.card)) *
        (numeratorPrincipalIndicator (nativeSignedRowProduct O T) +
          nativeWordSign true * numeratorPrincipalIndicator (-nativeSignedRowProduct O T)) = 0
      rw [hz, mul_zero]
    . intro hn
      exact False.elim (hn hO)
  have hsub : nativeEulerianMasks P G <= G.powerset := Finset.filter_subset _ _
  have ho : forall C : Finset (Prod Nat Nat), Membership.mem G.powerset C ->
      Not (Membership.mem (nativeEulerianMasks P G) C) -> f C C = 0 := by
    intro C hC hn
    have hCG := Finset.mem_powerset.mp hC
    have hbad : Not (forall p : Nat, Membership.mem P p ->
        nativePrimeVertexCycleDegree C p % 2 = 0) := by
      intro h
      exact hn ((native_eulerian_masks_mem_iff P G C).mpr (And.intro hCG h))
    have hz := native_phase_diagonal_indicator P hP C (hCG.trans hG) true
    rw [ite_eq_right hbad] at hz
    change (1 + (-1 : Real) ^ (C.card + C.card)) *
      (numeratorPrincipalIndicator (nativeSignedRowProduct C C) +
        nativeWordSign true * numeratorPrincipalIndicator (-nativeSignedRowProduct C C)) = 0
    rw [hz, mul_zero]
  have hm : (nativeEulerianMasks P G).sum (fun C => f C C) =
      2 * (nativeEulerianCount P G : Real) := by
    calc
      _ = (nativeEulerianMasks P G).sum (fun _ => (2 : Real)) := by
        apply Finset.sum_congr rfl
        intro C hC
        exact native_graph_positive_phase_paired_mask_eq_two_of_eulerian P hP G hG C hC
      _ = (nativeEulerianCount P G : Real) * 2 := by simp [nativeEulerianCount]
      _ = _ := mul_comm _ _
  have hall : G.powerset.sum (fun O => G.powerset.sum (fun T => f O T)) =
      2 * (nativeEulerianCount P G : Real) := by
    calc
      _ = G.powerset.sum (fun O => f O O) := Finset.sum_congr rfl hi
      _ = (nativeEulerianMasks P G).sum (fun C => f C C) :=
        (Finset.sum_subset hsub ho).symm
      _ = _ := hm
  rw [native_graph_phase_constant_word_sum_expansion]
  change (1 / (2 : Real) ^ (G.card + G.card + 1)) *
      G.powerset.sum (fun O => G.powerset.sum (fun T => f O T)) =
    (1 / (2 : Real) ^ (G.card + G.card + 1)) * (2 * (nativeEulerianCount P G : Real))
  rw [hall]

theorem native_graph_positive_phase_constant_word_conditional_eq_of_independent (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    2 * (nativeSignedPhaseWordRate G G (fun _ => true) (fun _ => true) true +
      nativeSignedPhaseWordRate G G (fun _ => false) (fun _ => false) true) =
      (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEulerianCount P G : Real)) := by
  rw [native_graph_positive_phase_constant_word_rate_eq_of_independent P hP hind G hG,
    pow_succ]
  have h2 : Not ((2 : Real) ^ (G.card + G.card) = 0) := pow_ne_zero _ (by norm_num)
  field_simp [h2]

theorem native_graph_positive_phase_agreement_rate_eq_of_independent (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    2 * nativeGraphPhaseAgreementRate G true = nativePositivePhaseCoincidenceFloor P G := by
  have hp := native_graph_positive_phase_constant_word_conditional_eq_of_independent P hP hind G hG
  have hc := native_phase_profile_conditional_rate_eq P hP G hG (fun _ => false) true
  unfold nativePositivePhaseCoincidenceFloor
  rw [<- hc]
  unfold nativeGraphPhaseAgreementRate
  linarith only [hp]

theorem native_graph_positive_phase_weight_ratio_tendsto_of_independent (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G true (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand true (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativePositivePhaseCoincidenceFloor P G)) := by
  rw [<- native_graph_positive_phase_agreement_rate_eq_of_independent P hP hind G hG]
  exact native_graph_mod_four_weight_conditional_ratio_tendsto P hP G hG hne true

theorem native_reservoir_positive_phase_weight_ratio_tendsto
    (R : Nat -> Prop) [DecidablePred R] (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p ->
      Membership.mem (nativePrimeVertexGapReservoirClass R) p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G true (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand true (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativePositivePhaseCoincidenceFloor P G)) := by
  have hp : forall p : Nat, Membership.mem P p -> Nat.Prime p :=
    fun p hm => (native_gap_reservoir_class_geometry R p (hP p hm)).1
  exact native_graph_positive_phase_weight_ratio_tendsto_of_independent P hp
    (native_gap_reservoir_class_finite_independent R P hP) G hG hne

theorem native_infinite_positive_phase_coincidence_family_in_reservoir
    (R : Nat -> Prop) [DecidablePred R]
    (hR : Not (Tendsto (fun N : Nat => primeEventProbability N R) atTop (nhds 0))) :
    And (Set.Infinite (nativePrimeVertexGapReservoirClass R))
      (And (forall p : Nat, Membership.mem (nativePrimeVertexGapReservoirClass R) p ->
          And (Nat.Prime p) (R p))
        (forall P : Finset Nat,
          (forall p : Nat, Membership.mem P p ->
            Membership.mem (nativePrimeVertexGapReservoirClass R) p) ->
          forall G : Finset (Prod Nat Nat), G <= nativePrimeVertexEdges P -> G.Nonempty ->
            Tendsto (fun U : Nat =>
              nativeGraphPhaseWeightAgreementMass G true (preciseCore U + 1)
                (preciseCore U * preciseCore U + 1) /
                nativeModuloFourBand true (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
              atTop (nhds (nativePositivePhaseCoincidenceFloor P G)))) := by
  have h := native_infinite_prime_gap_independent_family_in_reservoir R hR
  exact And.intro h.1 (And.intro h.2.1 (native_reservoir_positive_phase_weight_ratio_tendsto R))

theorem native_infinite_positive_phase_coincidence_family :
    And (Set.Infinite (nativePrimeVertexGapReservoirClass (fun _ => True)))
      (And (forall p : Nat,
          Membership.mem (nativePrimeVertexGapReservoirClass (fun _ => True)) p -> Nat.Prime p)
        (forall P : Finset Nat,
          (forall p : Nat, Membership.mem P p ->
            Membership.mem (nativePrimeVertexGapReservoirClass (fun _ => True)) p) ->
          forall G : Finset (Prod Nat Nat), G <= nativePrimeVertexEdges P -> G.Nonempty ->
            Tendsto (fun U : Nat =>
              nativeGraphPhaseWeightAgreementMass G true (preciseCore U + 1)
                (preciseCore U * preciseCore U + 1) /
                nativeModuloFourBand true (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
              atTop (nhds (nativePositivePhaseCoincidenceFloor P G)))) := by
  have h := native_infinite_prime_gap_independent_family
  exact And.intro h.1 (And.intro h.2.1
    (native_reservoir_positive_phase_weight_ratio_tendsto (fun _ => True)))

theorem native_triangle_positive_phase_floor (P : Finset Nat) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hpq : p < q) (hqr : q < r) :
    nativePositivePhaseCoincidenceFloor P {(p, q), (q, r), (p, r)} = 1 / 16 := by
  have hc : Not (nativePhaseProfileCompatible P {(p, q), (q, r), (p, r)}
      (fun _ => false) true) := by
    intro h
    have hh := (native_triangle_phase_profile_compatible_iff P p q r hp hq hr hpq hqr
      (fun _ => false) true).mp h
    rw [native_constant_profile_coefficient, native_phase_triangle_card p q r hpq hqr] at hh
    norm_num [nativeWordSign] at hh
  unfold nativePositivePhaseCoincidenceFloor
  rw [ite_eq_right hc, native_phase_triangle_eulerian_count P p q r hp hq hr hpq hqr,
    native_phase_triangle_card p q r hpq hqr]
  norm_num

theorem native_triangle_positive_phase_agreement_rate_lower_bound (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hpq : p < q) (hqr : q < r) :
    (1 / 16 : Real) <= 2 * nativeGraphPhaseAgreementRate {(p, q), (q, r), (p, r)} true := by
  have h := native_graph_positive_phase_agreement_rate_lower_bound P hP
    {(p, q), (q, r), (p, r)} (native_phase_triangle_support P p q r hp hq hr hpq hqr)
  rw [native_triangle_positive_phase_floor P p q r hp hq hr hpq hqr] at h
  exact h

theorem native_triangle_positive_phase_weight_ratio_tendsto_of_independent (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hpq : p < q) (hqr : q < r) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass {(p, q), (q, r), (p, r)} true (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand true (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / 16 : Real)) := by
  have hne : ({(p, q), (q, r), (p, r)} : Finset (Prod Nat Nat)).Nonempty :=
    Finset.card_pos.mp (by rw [native_phase_triangle_card p q r hpq hqr]; norm_num)
  have h := native_graph_positive_phase_weight_ratio_tendsto_of_independent P hP hind
    {(p, q), (q, r), (p, r)} (native_phase_triangle_support P p q r hp hq hr hpq hqr) hne
  rw [native_triangle_positive_phase_floor P p q r hp hq hr hpq hqr] at h
  exact h

end PrimeFactorOscillations.FiniteFieldIntegerSignature
