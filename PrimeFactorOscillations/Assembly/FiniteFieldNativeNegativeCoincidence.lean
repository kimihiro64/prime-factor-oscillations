/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeCoincidenceGap

/-! # Complete signed cancellation and negative-phase coincidence -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerCharacter
open FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeOddSquareRowObstruction (G : Finset (Prod Nat Nat)) : Prop :=
  Exists (fun r : Prod (Finset (Prod Nat Nat)) (Finset (Prod Nat Nat)) =>
    And (Membership.mem (nativeEvenSquareRowPairs G) r) (r.1.card % 2 = 1))

def nativeSquareRowParitySum (G : Finset (Prod Nat Nat)) : Real :=
  (nativeEvenSquareRowPairs G).sum (fun r => (-1 : Real) ^ r.1.card)

theorem native_mask_symmDiff_sign {I : Type*} [DecidableEq I] (S T : Finset I) :
    (-1 : Real) ^ (symmDiff S T).card = (-1 : Real) ^ S.card * (-1 : Real) ^ T.card := by
  have hc := native_mask_card_symmDiff_double_inter S T
  have hp : (-1 : Real) ^ (2 * (Inter.inter S T).card) = 1 := by
    rw [pow_mul]
    norm_num
  calc
    _ = (-1 : Real) ^ (symmDiff S T).card * 1 := (mul_one _).symm
    _ = (-1 : Real) ^ (symmDiff S T).card *
        (-1 : Real) ^ (2 * (Inter.inter S T).card) := by rw [hp]
    _ = (-1 : Real) ^ ((symmDiff S T).card + 2 * (Inter.inter S T).card) :=
      (pow_add _ _ _).symm
    _ = (-1 : Real) ^ (S.card + T.card) := congrArg (fun n : Nat => (-1 : Real) ^ n) hc
    _ = _ := pow_add _ _ _

theorem native_even_square_row_sum_translate (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (w : Prod (Finset (Prod Nat Nat)) (Finset (Prod Nat Nat)))
    (hw : Membership.mem (nativeEvenSquareRowPairs G) w)
    (f : Prod (Finset (Prod Nat Nat)) (Finset (Prod Nat Nat)) -> Real) :
    (nativeEvenSquareRowPairs G).sum f =
      (nativeEvenSquareRowPairs G).sum
        (fun r => f (symmDiff r.1 w.1, symmDiff r.2 w.2)) := by
  apply Finset.sum_bij'
    (fun r _ => (symmDiff r.1 w.1, symmDiff r.2 w.2))
    (fun r _ => (symmDiff r.1 w.1, symmDiff r.2 w.2))
  . intro r hr
    exact native_even_square_row_pairs_symmDiff_mem P hP G hG r w hr hw
  . intro r hr
    exact native_even_square_row_pairs_symmDiff_mem P hP G hG r w hr hw
  . intro r hr
    apply Prod.ext
    . exact symmDiff_symmDiff_cancel_right w.1 r.1
    . exact symmDiff_symmDiff_cancel_right w.2 r.2
  . intro r hr
    apply Prod.ext
    . exact symmDiff_symmDiff_cancel_right w.1 r.1
    . exact symmDiff_symmDiff_cancel_right w.2 r.2
  . intro r hr
    dsimp only
    simp only [symmDiff_symmDiff_cancel_right]

theorem native_square_row_parity_sum_zero_of_obstruction (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hodd : nativeOddSquareRowObstruction G) : nativeSquareRowParitySum G = 0 := by
  choose w hw using hodd
  have hpar : Not (w.1.card % 2 = 0) := by omega
  have hp : (-1 : Real) ^ w.1.card = -1 := by
    have hc := native_synchronized_sign_coefficient_parity w.1.card
    rw [ite_eq_right hpar] at hc
    linarith only [hc]
  have ht := native_even_square_row_sum_translate P hP G hG w hw.1
    (fun r => (-1 : Real) ^ r.1.card)
  have hs : (nativeEvenSquareRowPairs G).sum
      (fun r => (-1 : Real) ^ (symmDiff r.1 w.1).card) =
        -(nativeEvenSquareRowPairs G).sum (fun r => (-1 : Real) ^ r.1.card) := by
    calc
      _ = (nativeEvenSquareRowPairs G).sum (fun r => -((-1 : Real) ^ r.1.card)) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [native_mask_symmDiff_sign, hp, mul_neg_one]
      _ = _ := Finset.sum_neg_distrib _
  dsimp only at ht
  unfold nativeSquareRowParitySum
  linarith only [ht, hs]

theorem native_square_row_parity_sum_eq_count_of_no_obstruction
    (G : Finset (Prod Nat Nat)) (hno : Not (nativeOddSquareRowObstruction G)) :
    nativeSquareRowParitySum G = (nativeEvenSquareRowCount G : Real) := by
  unfold nativeSquareRowParitySum
  calc
    _ = (nativeEvenSquareRowPairs G).sum (fun _ => (1 : Real)) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hp : r.1.card % 2 = 0 := by
        have hn : Not (r.1.card % 2 = 1) := fun h =>
          hno (Exists.intro r (And.intro hr h))
        omega
      have hc := native_synchronized_sign_coefficient_parity r.1.card
      rw [ite_eq_left hp] at hc
      linarith only [hc]
    _ = _ := by simp [nativeEvenSquareRowCount]

theorem native_square_row_parity_sum_dichotomy (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    nativeSquareRowParitySum G =
      if nativeOddSquareRowObstruction G then 0 else (nativeEvenSquareRowCount G : Real) := by
  by_cases ho : nativeOddSquareRowObstruction G
  . rw [ite_eq_left ho]
    exact native_square_row_parity_sum_zero_of_obstruction P hP G hG ho
  . rw [ite_eq_right ho]
    exact native_square_row_parity_sum_eq_count_of_no_obstruction G ho

theorem native_signed_indicator_difference_eq_unsigned (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    numeratorPrincipalIndicator (nativeSignedRowProduct A B) -
        numeratorPrincipalIndicator (-nativeSignedRowProduct A B) =
      (-1 : Real) ^ A.card * (if IsSquare (nativeUnsignedRowProduct A B) then 1 else 0) := by
  have hU : 0 < nativeUnsignedRowProduct A B :=
    native_phase_row_unsigned_product_positive P hP A B hA hB
  have hD := native_signed_row_product_ne_zero P hP A B hA hB
  have h0 : IsSquare (nativeSignedRowProduct A B) <->
      And (IsSquare (nativeUnsignedRowProduct A B)) (A.card % 2 = 0) := by
    rw [native_signed_row_product_factorization]
    exact native_signed_positive_cast_square_iff _ hU A.card
  have hv : numeratorPrincipalIndicator (nativeSignedRowProduct A B) =
      if And (IsSquare (nativeUnsignedRowProduct A B)) (A.card % 2 = 0) then 1 else 0 := by
    rw [numerator_principal_indicator_int_eq_square _ hD]
    by_cases hd : IsSquare (nativeSignedRowProduct A B)
    . rw [ite_eq_left hd, ite_eq_left (h0.mp hd)]
    . have hn : Not (And (IsSquare (nativeUnsignedRowProduct A B)) (A.card % 2 = 0)) :=
        fun h => hd (h0.mpr h)
      rw [ite_eq_right hd, ite_eq_right hn]
  have hs := native_signed_agnostic_indicator_eq_unsigned P hP A B hA hB
  have hp : (-1 : Real) ^ A.card = if A.card % 2 = 0 then 1 else -1 := by
    simpa only [nativeWordSign, Bool.false_eq_true, ite_false] using
      native_word_sign_power_parity false A.card
  rw [hv] at hs
  rw [hv, hp]
  by_cases hsq : IsSquare (nativeUnsignedRowProduct A B) <;>
    by_cases he : A.card % 2 = 0
  all_goals simp only [hsq, he, and_self, and_true, and_false, ite_true, ite_false] at hs
  all_goals simp only [hsq, he, and_self, and_true, and_false, ite_true, ite_false]
  all_goals linarith only [hs]

theorem native_negative_even_square_row_paired_contribution (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    (1 + (-1 : Real) ^ (A.card + B.card)) *
      (numeratorPrincipalIndicator (nativeSignedRowProduct A B) +
        nativeWordSign false * numeratorPrincipalIndicator (-nativeSignedRowProduct A B)) =
      if And ((A.card + B.card) % 2 = 0) (IsSquare (nativeUnsignedRowProduct A B))
        then 2 * (-1 : Real) ^ A.card else 0 := by
  change (1 + (-1 : Real) ^ (A.card + B.card)) *
    (numeratorPrincipalIndicator (nativeSignedRowProduct A B) +
      (-1 : Real) * numeratorPrincipalIndicator (-nativeSignedRowProduct A B)) = _
  rw [neg_one_mul, <- sub_eq_add_neg,
    native_signed_indicator_difference_eq_unsigned P hP A B hA hB,
    native_synchronized_sign_coefficient_parity]
  by_cases hp : (A.card + B.card) % 2 = 0 <;>
    by_cases hs : IsSquare (nativeUnsignedRowProduct A B) <;> simp [hp, hs]

theorem native_even_square_row_signed_sum (G : Finset (Prod Nat Nat)) :
    G.powerset.sum (fun O => G.powerset.sum (fun T =>
      if And ((O.card + T.card) % 2 = 0) (IsSquare (nativeUnsignedRowProduct O T))
        then 2 * (-1 : Real) ^ O.card else 0)) = 2 * nativeSquareRowParitySum G := by
  have h : (nativeEvenSquareRowPairs G).sum (fun r => 2 * (-1 : Real) ^ r.1.card) =
      G.powerset.sum (fun O => G.powerset.sum (fun T =>
        if And ((O.card + T.card) % 2 = 0) (IsSquare (nativeUnsignedRowProduct O T))
          then 2 * (-1 : Real) ^ O.card else 0)) := by
    rw [nativeEvenSquareRowPairs, Finset.sum_filter]
    exact Finset.sum_product G.powerset G.powerset _
  calc
    _ = (nativeEvenSquareRowPairs G).sum (fun r => 2 * (-1 : Real) ^ r.1.card) := h.symm
    _ = 2 * (nativeEvenSquareRowPairs G).sum (fun r => (-1 : Real) ^ r.1.card) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := rfl


theorem native_even_square_row_count_positive (G : Finset (Prod Nat Nat)) :
    0 < nativeEvenSquareRowCount G := by
  unfold nativeEvenSquareRowCount
  apply Finset.card_pos.mpr
  refine Exists.intro (({} : Finset (Prod Nat Nat)), ({} : Finset (Prod Nat Nat))) ?_
  apply (native_even_square_row_pairs_mem_iff G _).mpr
  exact And.intro (Finset.empty_subset G) (And.intro (Finset.empty_subset G)
    (And.intro (by simp) (Exists.intro 1 (by simp [nativeUnsignedRowProduct]))))

theorem native_graph_negative_phase_constant_word_signed_count_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    nativeSignedPhaseWordRate G G (fun _ => true) (fun _ => true) false +
      nativeSignedPhaseWordRate G G (fun _ => false) (fun _ => false) false =
        (1 / (2 : Real) ^ (G.card + G.card + 1)) * (2 * nativeSquareRowParitySum G) := by
  rw [native_graph_phase_constant_word_sum_expansion]
  congr 1
  calc
    _ = G.powerset.sum (fun O => G.powerset.sum (fun T =>
        if And ((O.card + T.card) % 2 = 0) (IsSquare (nativeUnsignedRowProduct O T))
          then 2 * (-1 : Real) ^ O.card else 0)) := by
      apply Finset.sum_congr rfl
      intro O hO
      apply Finset.sum_congr rfl
      intro T hT
      exact native_negative_even_square_row_paired_contribution P hP O T
        ((Finset.mem_powerset.mp hO).trans hG) ((Finset.mem_powerset.mp hT).trans hG)
    _ = _ := native_even_square_row_signed_sum G

theorem native_graph_negative_phase_agreement_signed_count_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    2 * nativeGraphPhaseAgreementRate G false =
      (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) +
        (1 / (2 : Real) ^ (G.card + G.card)) * (2 * nativeSquareRowParitySum G) := by
  have hw : 2 * (nativeSignedPhaseWordRate G G (fun _ => true) (fun _ => true) false +
      nativeSignedPhaseWordRate G G (fun _ => false) (fun _ => false) false) =
      (1 / (2 : Real) ^ (G.card + G.card)) * (2 * nativeSquareRowParitySum G) := by
    rw [native_graph_negative_phase_constant_word_signed_count_eq P hP G hG, pow_succ]
    have h2 : Not ((2 : Real) ^ (G.card + G.card) = 0) := pow_ne_zero _ (by norm_num)
    field_simp [h2]
  have hc := native_phase_profile_conditional_rate_eq P hP G hG (fun _ => false) false
  rw [ite_eq_left (native_central_negative_phase_compatible P G)] at hc
  unfold nativeGraphPhaseAgreementRate
  linarith only [hw, hc]

theorem native_graph_negative_phase_agreement_dichotomy_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    2 * nativeGraphPhaseAgreementRate G false =
      (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) +
        if nativeOddSquareRowObstruction G then 0 else
          (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEvenSquareRowCount G : Real)) := by
  rw [native_graph_negative_phase_agreement_signed_count_eq P hP G hG,
    native_square_row_parity_sum_dichotomy P hP G hG]
  by_cases ho : nativeOddSquareRowObstruction G <;> simp [ho]

theorem native_negative_phase_agreement_eq_central_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    2 * nativeGraphPhaseAgreementRate G false =
        (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) <->
      nativeOddSquareRowObstruction G := by
  constructor
  . intro heq
    by_contra hno
    have hr := native_graph_negative_phase_agreement_dichotomy_eq P hP G hG
    rw [ite_eq_right hno] at hr
    have hK : 0 < (nativeEvenSquareRowCount G : Real) := by
      exact_mod_cast native_even_square_row_count_positive G
    have hp : 0 < (1 / (2 : Real) ^ (G.card + G.card)) *
        (2 * (nativeEvenSquareRowCount G : Real)) := by positivity
    linarith only [heq, hr, hp]
  . intro ho
    rw [native_graph_negative_phase_agreement_dichotomy_eq P hP G hG, ite_eq_left ho, add_zero]

theorem native_graph_negative_phase_weight_dichotomy_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hne : G.Nonempty) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G false (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand false (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds
        ((1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) +
          if nativeOddSquareRowObstruction G then 0 else
            (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEvenSquareRowCount G : Real)))) := by
  rw [<- native_graph_negative_phase_agreement_dichotomy_eq P hP G hG]
  exact native_graph_mod_four_weight_conditional_ratio_tendsto P hP G hG hne false

theorem native_odd_eulerian_square_row_obstruction (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hC : Membership.mem (nativeEulerianMasks P G) C)
    (hodd : C.card % 2 = 1) : nativeOddSquareRowObstruction G := by
  exact Exists.intro (C, C)
    (And.intro (native_eulerian_diagonal_square_pair_mem P hP G hG C hC) hodd)

theorem native_central_positive_compatible_of_no_row_obstruction (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hno : Not (nativeOddSquareRowObstruction G)) :
    nativePhaseProfileCompatible P G (fun _ => false) true := by
  intro C hC
  have hn : Not (C.card % 2 = 1) := fun ho =>
    hno (native_odd_eulerian_square_row_obstruction P hP G hG C hC ho)
  have he : C.card % 2 = 0 := by omega
  rw [native_constant_profile_coefficient]
  change (-1 : Real) ^ C.card = (1 : Real) ^ C.card
  rw [one_pow]
  have hc := native_synchronized_sign_coefficient_parity C.card
  rw [ite_eq_left he] at hc
  linarith only [hc]

theorem native_graph_phase_agreement_eq_of_no_row_obstruction (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hno : Not (nativeOddSquareRowObstruction G)) :
    2 * nativeGraphPhaseAgreementRate G false = 2 * nativeGraphPhaseAgreementRate G true := by
  rw [native_graph_negative_phase_agreement_dichotomy_eq P hP G hG,
    native_graph_positive_phase_agreement_count_eq P hP G hG, ite_eq_right hno,
    ite_eq_left (native_central_positive_compatible_of_no_row_obstruction P hP G hG hno)]

theorem native_graph_two_phase_agreement_dichotomy (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    Or
      (And (Not (nativeOddSquareRowObstruction G))
        (2 * nativeGraphPhaseAgreementRate G false = 2 * nativeGraphPhaseAgreementRate G true))
      (And (nativeOddSquareRowObstruction G)
        (2 * nativeGraphPhaseAgreementRate G false =
          (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real))) := by
  by_cases ho : nativeOddSquareRowObstruction G
  . exact Or.inr (And.intro ho ((native_negative_phase_agreement_eq_central_iff P hP G hG).mpr ho))
  . exact Or.inl (And.intro ho (native_graph_phase_agreement_eq_of_no_row_obstruction P hP G hG ho))

end PrimeFactorOscillations.FiniteFieldIntegerSignature
