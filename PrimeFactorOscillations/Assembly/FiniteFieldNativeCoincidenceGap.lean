/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativePositiveCoincidence
import PrimeFactorOscillations.Definitions.NativePrimeSquareMaskRelations
import PrimeFactorOscillations.Helpers.NativePrimeSquareMaskTranslation

/-! # Exact square-relation counts and isolation of the native coincidence floor -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerCharacter
open FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

theorem native_even_square_row_pairs_mem_iff (G : Finset (Prod Nat Nat))
    (r : Prod (Finset (Prod Nat Nat)) (Finset (Prod Nat Nat))) :
    Membership.mem (nativeEvenSquareRowPairs G) r <->
      And (r.1 <= G) (And (r.2 <= G)
        (And ((r.1.card + r.2.card) % 2 = 0) (IsSquare (nativeUnsignedRowProduct r.1 r.2)))) := by
  cases r with
  | mk O T =>
      rw [nativeEvenSquareRowPairs, Finset.mem_filter]
      constructor
      . intro h
        have hp : And (Membership.mem G.powerset O) (Membership.mem G.powerset T) :=
          Finset.mem_product.mp h.1
        exact And.intro (Finset.mem_powerset.mp hp.1)
          (And.intro (Finset.mem_powerset.mp hp.2) h.2)
      . intro h
        exact And.intro
          (Finset.mem_product.mpr (And.intro (Finset.mem_powerset.mpr h.1)
            (Finset.mem_powerset.mpr h.2.1))) h.2.2

theorem native_signed_agnostic_indicator_eq_unsigned (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    numeratorPrincipalIndicator (nativeSignedRowProduct A B) +
        numeratorPrincipalIndicator (-nativeSignedRowProduct A B) =
      if IsSquare (nativeUnsignedRowProduct A B) then 1 else 0 := by
  have hU : 0 < nativeUnsignedRowProduct A B :=
    native_phase_row_unsigned_product_positive P hP A B hA hB
  have hD := native_signed_row_product_ne_zero P hP A B hA hB
  have h0 : IsSquare (nativeSignedRowProduct A B) <->
      And (IsSquare (nativeUnsignedRowProduct A B)) (A.card % 2 = 0) := by
    rw [native_signed_row_product_factorization]
    exact native_signed_positive_cast_square_iff _ hU A.card
  have hfactor : -nativeSignedRowProduct A B =
      (-1 : Int) ^ (A.card + 1) * (nativeUnsignedRowProduct A B : Int) := by
    rw [native_signed_row_product_factorization, pow_succ]
    unfold nativeUnsignedRowProduct
    ring
  have h1 : IsSquare (-nativeSignedRowProduct A B) <->
      And (IsSquare (nativeUnsignedRowProduct A B)) ((A.card + 1) % 2 = 0) := by
    rw [hfactor]
    exact native_signed_positive_cast_square_iff _ hU (A.card + 1)
  rw [numerator_principal_indicator_int_eq_square _ hD,
    numerator_principal_indicator_int_eq_square _ (neg_ne_zero.mpr hD)]
  by_cases hu : IsSquare (nativeUnsignedRowProduct A B)
  . by_cases hp : A.card % 2 = 0
    . have hsD : IsSquare (nativeSignedRowProduct A B) := h0.mpr (And.intro hu hp)
      have hsN : Not (IsSquare (-nativeSignedRowProduct A B)) := by
        intro hs
        have he := (h1.mp hs).2
        omega
      rw [ite_eq_left hsD, ite_eq_right hsN, ite_eq_left hu]
      norm_num
    . have hsD : Not (IsSquare (nativeSignedRowProduct A B)) :=
        fun hs => hp (h0.mp hs).2
      have he : (A.card + 1) % 2 = 0 := by omega
      have hsN : IsSquare (-nativeSignedRowProduct A B) := h1.mpr (And.intro hu he)
      rw [ite_eq_right hsD, ite_eq_left hsN, ite_eq_left hu]
      norm_num
  . have hsD : Not (IsSquare (nativeSignedRowProduct A B)) := fun hs => hu (h0.mp hs).1
    have hsN : Not (IsSquare (-nativeSignedRowProduct A B)) := fun hs => hu (h1.mp hs).1
    rw [ite_eq_right hsD, ite_eq_right hsN, ite_eq_right hu]
    norm_num

theorem native_synchronized_sign_coefficient_parity (n : Nat) :
    1 + (-1 : Real) ^ n = if n % 2 = 0 then 2 else 0 := by
  have h : (-1 : Real) ^ n = if n % 2 = 0 then 1 else -1 := by
    simpa only [nativeWordSign, Bool.false_eq_true, ite_false] using native_word_sign_power_parity false n
  rw [h]
  by_cases hn : n % 2 = 0 <;> norm_num [hn]

theorem native_even_square_row_paired_contribution (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    (1 + (-1 : Real) ^ (A.card + B.card)) *
      (numeratorPrincipalIndicator (nativeSignedRowProduct A B) +
        nativeWordSign true * numeratorPrincipalIndicator (-nativeSignedRowProduct A B)) =
      if And ((A.card + B.card) % 2 = 0) (IsSquare (nativeUnsignedRowProduct A B))
        then 2 else 0 := by
  change (1 + (-1 : Real) ^ (A.card + B.card)) *
    (numeratorPrincipalIndicator (nativeSignedRowProduct A B) +
      (1 : Real) * numeratorPrincipalIndicator (-nativeSignedRowProduct A B)) = _
  rw [one_mul, native_signed_agnostic_indicator_eq_unsigned P hP A B hA hB,
    native_synchronized_sign_coefficient_parity]
  by_cases hp : (A.card + B.card) % 2 = 0 <;>
    by_cases hs : IsSquare (nativeUnsignedRowProduct A B) <;> simp [hp, hs]

theorem native_even_square_row_pairs_card_sum (G : Finset (Prod Nat Nat)) :
    G.powerset.sum (fun O => G.powerset.sum (fun T =>
      if And ((O.card + T.card) % 2 = 0) (IsSquare (nativeUnsignedRowProduct O T))
        then (2 : Real) else 0)) = 2 * (nativeEvenSquareRowCount G : Real) := by
  have h : (nativeEvenSquareRowPairs G).sum (fun _ => (2 : Real)) =
      G.powerset.sum (fun O => G.powerset.sum (fun T =>
        if And ((O.card + T.card) % 2 = 0) (IsSquare (nativeUnsignedRowProduct O T))
          then (2 : Real) else 0)) := by
    rw [nativeEvenSquareRowPairs, Finset.sum_filter]
    exact Finset.sum_product G.powerset G.powerset _
  calc
    _ = (nativeEvenSquareRowPairs G).sum (fun _ => (2 : Real)) := h.symm
    _ = (nativeEvenSquareRowCount G : Real) * 2 := by simp [nativeEvenSquareRowCount]
    _ = _ := mul_comm _ _

theorem native_graph_positive_phase_constant_word_count_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    nativeSignedPhaseWordRate G G (fun _ => true) (fun _ => true) true +
      nativeSignedPhaseWordRate G G (fun _ => false) (fun _ => false) true =
        (1 / (2 : Real) ^ (G.card + G.card + 1)) *
          (2 * (nativeEvenSquareRowCount G : Real)) := by
  rw [native_graph_phase_constant_word_sum_expansion]
  congr 1
  calc
    _ = G.powerset.sum (fun O => G.powerset.sum (fun T =>
        if And ((O.card + T.card) % 2 = 0) (IsSquare (nativeUnsignedRowProduct O T))
          then (2 : Real) else 0)) := by
      apply Finset.sum_congr rfl
      intro O hO
      apply Finset.sum_congr rfl
      intro T hT
      exact native_even_square_row_paired_contribution P hP O T
        ((Finset.mem_powerset.mp hO).trans hG) ((Finset.mem_powerset.mp hT).trans hG)
    _ = _ := native_even_square_row_pairs_card_sum G

theorem native_graph_positive_phase_agreement_count_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    2 * nativeGraphPhaseAgreementRate G true =
      (if nativePhaseProfileCompatible P G (fun _ => false) true then
        (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) else 0) +
      (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEvenSquareRowCount G : Real)) := by
  have hw : 2 * (nativeSignedPhaseWordRate G G (fun _ => true) (fun _ => true) true +
      nativeSignedPhaseWordRate G G (fun _ => false) (fun _ => false) true) =
      (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEvenSquareRowCount G : Real)) := by
    rw [native_graph_positive_phase_constant_word_count_eq P hP G hG, pow_succ]
    have h2 : Not ((2 : Real) ^ (G.card + G.card) = 0) := pow_ne_zero _ (by norm_num)
    field_simp [h2]
  have hc := native_phase_profile_conditional_rate_eq P hP G hG (fun _ => false) true
  unfold nativeGraphPhaseAgreementRate
  linarith only [hw, hc]

theorem native_graph_positive_phase_weight_count_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G true (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand true (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds
        ((if nativePhaseProfileCompatible P G (fun _ => false) true then
          (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) else 0) +
        (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEvenSquareRowCount G : Real)))) := by
  rw [<- native_graph_positive_phase_agreement_count_eq P hP G hG]
  exact native_graph_mod_four_weight_conditional_ratio_tendsto P hP G hG hne true


def nativeNoExtraEvenSquareRows (G : Finset (Prod Nat Nat)) : Prop :=
  forall r : Prod (Finset (Prod Nat Nat)) (Finset (Prod Nat Nat)),
    Membership.mem (nativeEvenSquareRowPairs G) r -> r.1 = r.2

theorem native_even_square_row_pairs_symmDiff_mem (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (r s : Prod (Finset (Prod Nat Nat)) (Finset (Prod Nat Nat)))
    (hr : Membership.mem (nativeEvenSquareRowPairs G) r)
    (hs : Membership.mem (nativeEvenSquareRowPairs G) s) :
    Membership.mem (nativeEvenSquareRowPairs G)
      (symmDiff r.1 s.1, symmDiff r.2 s.2) := by
  have h0 := (native_even_square_row_pairs_mem_iff G r).mp hr
  have h1 := (native_even_square_row_pairs_mem_iff G s).mp hs
  apply (native_even_square_row_pairs_mem_iff G _).mpr
  exact And.intro (native_mask_symmDiff_subset _ _ G h0.1 h1.1)
    (And.intro (native_mask_symmDiff_subset _ _ G h0.2.1 h1.2.1)
      (And.intro (native_even_row_pair_symmDiff_parity _ _ _ _ h0.2.2.1 h1.2.2.1)
        (native_unsigned_square_pair_symmDiff_closed P hP _ _ _ _
          (h0.1.trans hG) (h0.2.1.trans hG) h0.2.2.2 h1.2.2.2)))

theorem native_eulerian_diagonal_square_pair_mem (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hC : Membership.mem (nativeEulerianMasks P G) C) :
    Membership.mem (nativeEvenSquareRowPairs G) (C, C) := by
  have hh := (native_eulerian_masks_mem_iff P G C).mp hC
  apply (native_even_square_row_pairs_mem_iff G (C, C)).mpr
  exact And.intro hh.1 (And.intro hh.1 (And.intro (by dsimp; omega)
    ((native_diagonal_unsigned_isSquare_iff P hP C (hh.1.trans hG)).mpr hh.2)))

theorem native_diagonal_square_pair_mem_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) :
    Membership.mem (nativeEvenSquareRowPairs G) (C, C) <->
      Membership.mem (nativeEulerianMasks P G) C := by
  constructor
  . intro h
    have hh := (native_even_square_row_pairs_mem_iff G (C, C)).mp h
    apply (native_eulerian_masks_mem_iff P G C).mpr
    exact And.intro hh.1
      ((native_diagonal_unsigned_isSquare_iff P hP C (hh.1.trans hG)).mp hh.2.2.2)
  . exact native_eulerian_diagonal_square_pair_mem P hP G hG C

theorem native_even_square_row_count_eq_of_no_extra (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hno : nativeNoExtraEvenSquareRows G) :
    nativeEvenSquareRowCount G = nativeEulerianCount P G := by
  have heq : nativeEvenSquareRowPairs G =
      (nativeEulerianMasks P G).image (fun C => (C, C)) := by
    ext r
    constructor
    . intro hr
      have hh := hno r hr
      have hd : r = (r.1, r.1) := Prod.ext rfl hh.symm
      apply Finset.mem_image.mpr
      refine Exists.intro r.1 (And.intro ?_ hd.symm)
      apply (native_diagonal_square_pair_mem_iff P hP G hG r.1).mp
      rw [<- hd]
      exact hr
    . intro hr
      choose C hC using Finset.mem_image.mp hr
      rw [<- hC.2]
      exact native_eulerian_diagonal_square_pair_mem P hP G hG C hC.1
  unfold nativeEvenSquareRowCount nativeEulerianCount
  rw [heq]
  apply Finset.card_image_of_injective
  intro C A h
  exact congrArg Prod.fst h

theorem native_even_square_row_count_ge_double_of_extra (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (r : Prod (Finset (Prod Nat Nat)) (Finset (Prod Nat Nat)))
    (hr : Membership.mem (nativeEvenSquareRowPairs G) r) (hoff : Not (r.1 = r.2)) :
    2 * nativeEulerianCount P G <= nativeEvenSquareRowCount G := by
  let D := (nativeEulerianMasks P G).image (fun C => (C, C))
  let F := (nativeEulerianMasks P G).image
    (fun C => (symmDiff r.1 C, symmDiff r.2 C))
  have hD : D <= nativeEvenSquareRowPairs G := by
    intro q hq
    choose C hC using Finset.mem_image.mp hq
    rw [<- hC.2]
    exact native_eulerian_diagonal_square_pair_mem P hP G hG C hC.1
  have hF : F <= nativeEvenSquareRowPairs G := by
    intro q hq
    choose C hC using Finset.mem_image.mp hq
    rw [<- hC.2]
    exact native_even_square_row_pairs_symmDiff_mem P hP G hG r (C, C) hr
      (native_eulerian_diagonal_square_pair_mem P hP G hG C hC.1)
  have hcD : D.card = nativeEulerianCount P G := by
    apply Finset.card_image_of_injective
    intro C A h
    exact congrArg Prod.fst h
  have hcF : F.card = nativeEulerianCount P G := by
    apply Finset.card_image_of_injective
    intro C A h
    exact native_mask_symmDiff_left_injective r.1 (congrArg Prod.fst h)
  have hd : Disjoint D F := Finset.disjoint_left.mpr (by
    intro q hqD hqF
    choose C hC using Finset.mem_image.mp hqD
    choose A hA using Finset.mem_image.mp hqF
    have he : (C, C) = (symmDiff r.1 A, symmDiff r.2 A) := hC.2.trans hA.2.symm
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    exact hoff (native_mask_symmDiff_right_cancel r.1 r.2 A (hfst.symm.trans hsnd)))
  have hsub : Union.union D F <= nativeEvenSquareRowPairs G := by
    intro q hq
    rcases Finset.mem_union.mp hq with h | h
    . exact hD h
    . exact hF h
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, hcD, hcF] at hc
  change 2 * nativeEulerianCount P G <= (nativeEvenSquareRowPairs G).card
  omega

theorem native_positive_phase_floor_gap_of_extra (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (r : Prod (Finset (Prod Nat Nat)) (Finset (Prod Nat Nat)))
    (hr : Membership.mem (nativeEvenSquareRowPairs G) r) (hoff : Not (r.1 = r.2)) :
    nativePositivePhaseCoincidenceFloor P G +
        (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEulerianCount P G : Real)) <=
      2 * nativeGraphPhaseAgreementRate G true := by
  have hn := native_even_square_row_count_ge_double_of_extra P hP G hG r hr hoff
  have hnR : 2 * (nativeEulerianCount P G : Real) <= (nativeEvenSquareRowCount G : Real) := by
    exact_mod_cast hn
  have hm : 0 <= (1 / (2 : Real) ^ (G.card + G.card)) := by positivity
  have hs := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnR (by norm_num : (0 : Real) <= 2)) hm
  rw [native_graph_positive_phase_agreement_count_eq P hP G hG]
  unfold nativePositivePhaseCoincidenceFloor
  linarith only [hs]

theorem native_positive_phase_floor_eq_iff_no_extra (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    2 * nativeGraphPhaseAgreementRate G true = nativePositivePhaseCoincidenceFloor P G <->
      nativeNoExtraEvenSquareRows G := by
  constructor
  . intro heq r hr
    by_contra hoff
    have hg := native_positive_phase_floor_gap_of_extra P hP G hG r hr hoff
    have hN : 0 < (nativeEulerianCount P G : Real) := by
      exact_mod_cast native_eulerian_count_positive P G
    have hpos : 0 < (1 / (2 : Real) ^ (G.card + G.card)) *
        (2 * (nativeEulerianCount P G : Real)) := by positivity
    linarith only [hg, heq, hpos]
  . intro hno
    rw [native_graph_positive_phase_agreement_count_eq P hP G hG,
      native_even_square_row_count_eq_of_no_extra P hP G hG hno]
    rfl

theorem native_positive_phase_floor_isolated (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    Or (2 * nativeGraphPhaseAgreementRate G true = nativePositivePhaseCoincidenceFloor P G)
      (nativePositivePhaseCoincidenceFloor P G +
        (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEulerianCount P G : Real)) <=
          2 * nativeGraphPhaseAgreementRate G true) := by
  by_cases hno : nativeNoExtraEvenSquareRows G
  . exact Or.inl ((native_positive_phase_floor_eq_iff_no_extra P hP G hG).mpr hno)
  . right
    have hex : Exists (fun r : Prod (Finset (Prod Nat Nat)) (Finset (Prod Nat Nat)) =>
        And (Membership.mem (nativeEvenSquareRowPairs G) r) (Not (r.1 = r.2))) := by
      by_contra hn
      apply hno
      intro r hr
      by_contra hoff
      exact hn (Exists.intro r (And.intro hr hoff))
    choose r hr using hex
    exact native_positive_phase_floor_gap_of_extra P hP G hG r hr.1 hr.2

theorem native_positive_phase_weight_limit_isolated (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty) :
    And (Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G true (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand true (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (2 * nativeGraphPhaseAgreementRate G true)))
      (Or (2 * nativeGraphPhaseAgreementRate G true = nativePositivePhaseCoincidenceFloor P G)
        (nativePositivePhaseCoincidenceFloor P G +
          (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEulerianCount P G : Real)) <=
            2 * nativeGraphPhaseAgreementRate G true)) := by
  exact And.intro (native_graph_mod_four_weight_conditional_ratio_tendsto P hP G hG hne true)
    (native_positive_phase_floor_isolated P hP G hG)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
