/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeGraphCoincidenceEvents
import PrimeFactorOscillations.Assembly.FiniteFieldNativeWordLaw
import PrimeFactorOscillations.Helpers.NativePrimeEvenCycleMasks

/-! # Sharp universal native graph-coincidence floor

Odd paired masks vanish before positivity is used. The two constant-sign
words are combined before their nonnegative mask coefficients are estimated.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

theorem native_graph_square_indicator_nonneg (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    0 <= numeratorPrincipalIndicator (nativeSignedRowProduct A B) := by
  rw [numerator_principal_indicator_int_eq_square _
    (native_signed_row_product_ne_zero P hP A B hA hB)]
  by_cases hs : IsSquare (nativeSignedRowProduct A B) <;> simp [hs]

theorem native_graph_cycle_indicator_eq_one (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hC : Membership.mem (nativeEvenCycleMasks P G) C) :
    numeratorPrincipalIndicator (nativeSignedRowProduct C C) = 1 := by
  have hc := (native_even_cycle_masks_mem_iff P G C).mp hC
  have hs := hc.1.trans hG
  have hsq := native_signed_cycle_product_isSquare P C hs hc.2.1 hc.2.2
  rw [numerator_principal_indicator_int_eq_square _
    (native_signed_row_product_ne_zero P hP C C hs hs), ite_eq_left hsq]

theorem native_graph_zero_mask_nonneg (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (S : Finset (Prod Nat Nat)) (hS : Membership.mem G.powerset S) :
    0 <= (-1 : Real) ^ S.card * numeratorPrincipalIndicator (nativeSignedRowProduct S S) := by
  have hs := (Finset.mem_powerset.mp hS).trans hG
  by_cases heven : S.card % 2 = 0
  . have he : S.card = 2 * (S.card / 2) := by omega
    have hp : (-1 : Real) ^ S.card = 1 := by
      calc
        _ = (-1 : Real) ^ (2 * (S.card / 2)) :=
          congrArg (fun n : Nat => (-1 : Real) ^ n) he
        _ = 1 := by rw [pow_mul]; norm_num
    rw [hp, one_mul]
    exact native_graph_square_indicator_nonneg P hP S S hs hs
  . have hodd : S.card % 2 = 1 := by omega
    have hneg := native_signed_paired_row_product_neg_of_odd P hP S hs hodd
    have hnsq : Not (IsSquare (nativeSignedRowProduct S S)) := by
      intro h
      cases h with
      | intro k hk =>
        have hnon : 0 <= nativeSignedRowProduct S S := by
          rw [hk]
          exact mul_self_nonneg k
        exact (not_le_of_gt hneg) hnon
    simpa only [numerator_principal_indicator_int_eq_square _
      (native_signed_row_product_ne_zero P hP S S hs hs),
      ite_eq_right hnsq, mul_zero] using (le_refl (0 : Real))

theorem native_graph_zero_mask_eq_one_of_cycle (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hC : Membership.mem (nativeEvenCycleMasks P G) C) :
    (-1 : Real) ^ C.card * numeratorPrincipalIndicator (nativeSignedRowProduct C C) = 1 := by
  have hc := ((native_even_cycle_masks_mem_iff P G C).mp hC).2.2
  have he : C.card = 2 * (C.card / 2) := by omega
  have hp : (-1 : Real) ^ C.card = 1 := by
    calc
      _ = (-1 : Real) ^ (2 * (C.card / 2)) :=
        congrArg (fun n : Nat => (-1 : Real) ^ n) he
      _ = 1 := by rw [pow_mul]; norm_num
  rw [hp, native_graph_cycle_indicator_eq_one P hP G hG C hC, one_mul]

theorem native_graph_zero_rate_lower_bound (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real) <=
      nativeGraphZeroTraceRate G := by
  let f := fun C : Finset (Prod Nat Nat) => (-1 : Real) ^ C.card *
    numeratorPrincipalIndicator (nativeSignedRowProduct C C)
  have hsub : nativeEvenCycleMasks P G <= G.powerset := Finset.filter_subset _ _
  have hm : (nativeEvenCycleMasks P G).sum f = (nativeEvenCycleCount P G : Real) := by
    calc
      _ = (nativeEvenCycleMasks P G).sum (fun _ => (1 : Real)) := by
        apply Finset.sum_congr rfl
        intro C hC
        exact native_graph_zero_mask_eq_one_of_cycle P hP G hG C hC
      _ = _ := by simp [nativeEvenCycleCount]
  have hs : (nativeEvenCycleMasks P G).sum f <= G.powerset.sum f :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun S hS _ => native_graph_zero_mask_nonneg P hP G hG S hS)
  rw [hm] at hs
  change (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real) <=
    (1 / (2 : Real) ^ G.card) * G.powerset.sum f
  exact mul_le_mul_of_nonneg_left hs (by positivity)

theorem native_graph_constant_word_sum_expansion (G : Finset (Prod Nat Nat)) :
    nativeSignedGeneralWordRate G G (fun _ => true) (fun _ => true) +
      nativeSignedGeneralWordRate G G (fun _ => false) (fun _ => false) =
        (1 / (2 : Real) ^ (G.card + G.card)) *
          G.powerset.sum (fun O => G.powerset.sum (fun T =>
            (1 + (-1 : Real) ^ (O.card + T.card)) *
              numeratorPrincipalIndicator (nativeSignedRowProduct O T))) := by
  have ht (O T : Finset (Prod Nat Nat)) :
      nativeSignedWordMaskCoefficient O T (fun _ => true) (fun _ => true) = 1 := by
    simp [nativeSignedWordMaskCoefficient, nativeWordSign]
  have hn (O T : Finset (Prod Nat Nat)) :
      nativeSignedWordMaskCoefficient O T (fun _ => false) (fun _ => false) =
        (-1 : Real) ^ (O.card + T.card) := by
    simp [nativeSignedWordMaskCoefficient, nativeWordSign, Finset.prod_const, pow_add]
  unfold nativeSignedGeneralWordRate
  simp only [ht, hn, one_mul]
  rw [<- mul_add, <- Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro O _
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem native_graph_paired_mask_nonneg (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    0 <= (1 + (-1 : Real) ^ (A.card + B.card)) *
      numeratorPrincipalIndicator (nativeSignedRowProduct A B) := by
  have hs : ((-1 : Real) ^ (A.card + B.card)) ^ 2 = 1 := by
    rw [<- pow_mul, Nat.mul_comm (A.card + B.card) 2, pow_mul]
    norm_num
  have hc : 0 <= 1 + (-1 : Real) ^ (A.card + B.card) := by
    nlinarith only [hs, sq_nonneg ((-1 : Real) ^ (A.card + B.card) + 1)]
  exact mul_nonneg hc (native_graph_square_indicator_nonneg P hP A B hA hB)

theorem native_graph_paired_mask_eq_two_of_cycle (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hC : Membership.mem (nativeEvenCycleMasks P G) C) :
    (1 + (-1 : Real) ^ (C.card + C.card)) *
      numeratorPrincipalIndicator (nativeSignedRowProduct C C) = 2 := by
  rw [native_graph_cycle_indicator_eq_one P hP G hG C hC, mul_one]
  have he : C.card + C.card = 2 * C.card := by omega
  rw [he, pow_mul]
  norm_num

theorem native_graph_constant_word_rate_lower_bound (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEvenCycleCount P G : Real)) <=
      nativeSignedGeneralWordRate G G (fun _ => true) (fun _ => true) +
        nativeSignedGeneralWordRate G G (fun _ => false) (fun _ => false) := by
  let f := fun O T : Finset (Prod Nat Nat) =>
    (1 + (-1 : Real) ^ (O.card + T.card)) *
      numeratorPrincipalIndicator (nativeSignedRowProduct O T)
  have hn : forall O : Finset (Prod Nat Nat), Membership.mem G.powerset O ->
      forall T : Finset (Prod Nat Nat), Membership.mem G.powerset T -> 0 <= f O T := by
    intro O hO T hT
    exact native_graph_paired_mask_nonneg P hP O T
      ((Finset.mem_powerset.mp hO).trans hG) ((Finset.mem_powerset.mp hT).trans hG)
  have hi : forall O : Finset (Prod Nat Nat), Membership.mem G.powerset O ->
      f O O <= G.powerset.sum (fun T => f O T) := by
    intro O hO
    exact Finset.single_le_sum (fun T hT => hn O hO T hT) hO
  have hsub : nativeEvenCycleMasks P G <= G.powerset := Finset.filter_subset _ _
  have hm : (nativeEvenCycleMasks P G).sum (fun C => f C C) =
      2 * (nativeEvenCycleCount P G : Real) := by
    calc
      _ = (nativeEvenCycleMasks P G).sum (fun _ => (2 : Real)) := by
        apply Finset.sum_congr rfl
        intro C hC
        exact native_graph_paired_mask_eq_two_of_cycle P hP G hG C hC
      _ = (nativeEvenCycleCount P G : Real) * 2 := by simp [nativeEvenCycleCount]
      _ = _ := mul_comm _ _
  have hd : (nativeEvenCycleMasks P G).sum (fun C => f C C) <=
      G.powerset.sum (fun C => f C C) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun C hC _ => hn C hC C hC)
  rw [hm] at hd
  have hall : 2 * (nativeEvenCycleCount P G : Real) <=
      G.powerset.sum (fun O => G.powerset.sum (fun T => f O T)) :=
    hd.trans (Finset.sum_le_sum (fun O hO => hi O hO))
  rw [native_graph_constant_word_sum_expansion]
  change (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEvenCycleCount P G : Real)) <=
    (1 / (2 : Real) ^ (G.card + G.card)) *
      G.powerset.sum (fun O => G.powerset.sum (fun T => f O T))
  exact mul_le_mul_of_nonneg_left hall (by positivity)

theorem native_graph_agreement_rate_lower_bound (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    (nativeEvenCycleCount P G : Real) *
      (1 / (2 : Real) ^ G.card + 2 / (2 : Real) ^ (G.card + G.card)) <=
        nativeGraphAgreementRate G := by
  calc
    _ = (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real) +
        (1 / (2 : Real) ^ (G.card + G.card)) *
          (2 * (nativeEvenCycleCount P G : Real)) := by ring
    _ <= nativeGraphZeroTraceRate G +
        (nativeSignedGeneralWordRate G G (fun _ => true) (fun _ => true) +
          nativeSignedGeneralWordRate G G (fun _ => false) (fun _ => false)) :=
      add_le_add (native_graph_zero_rate_lower_bound P hP G hG)
        (native_graph_constant_word_rate_lower_bound P hP G hG)
    _ = nativeGraphAgreementRate G := by
      unfold nativeGraphAgreementRate
      ring

theorem native_graph_agreement_limit_lower_bound (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) :
    And
      (Tendsto (fun U : Nat =>
        nativeGraphAgreementMass G (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
        atTop (nhds (nativeGraphAgreementRate G)))
      ((nativeEvenCycleCount P G : Real) *
        (1 / (2 : Real) ^ G.card + 2 / (2 : Real) ^ (G.card + G.card)) <=
          nativeGraphAgreementRate G) :=
  And.intro (native_graph_agreement_ratio_tendsto P hP G hG hne)
    (native_graph_agreement_rate_lower_bound P hP G hG)

theorem native_graph_noncycle_indicator_eq_zero (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P) (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (hn : Not (nativeSignedCycleMask P A B)) :
    numeratorPrincipalIndicator (nativeSignedRowProduct A B) = 0 := by
  have hnsq : Not (IsSquare (nativeSignedRowProduct A B)) := by
    intro h
    exact hn ((native_signed_row_product_isSquare_iff P hP hind A B hA hB).mp h)
  rw [numerator_principal_indicator_int_eq_square _
    (native_signed_row_product_ne_zero P hP A B hA hB), ite_eq_right hnsq]

theorem native_graph_zero_rate_eq_of_independent (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    nativeGraphZeroTraceRate G =
      (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real) := by
  let f := fun C : Finset (Prod Nat Nat) => (-1 : Real) ^ C.card *
    numeratorPrincipalIndicator (nativeSignedRowProduct C C)
  have hsub : nativeEvenCycleMasks P G <= G.powerset := Finset.filter_subset _ _
  have ho : forall C : Finset (Prod Nat Nat), Membership.mem G.powerset C ->
      Not (Membership.mem (nativeEvenCycleMasks P G) C) -> f C = 0 := by
    intro C hC hn
    have hCG := Finset.mem_powerset.mp hC
    have hs := hCG.trans hG
    have hbad : Not (nativeSignedCycleMask P C C) := by
      intro h
      exact hn ((native_even_cycle_masks_mem_iff P G C).mpr (And.intro hCG h.2))
    change (-1 : Real) ^ C.card *
      numeratorPrincipalIndicator (nativeSignedRowProduct C C) = 0
    rw [native_graph_noncycle_indicator_eq_zero P hP hind C C hs hs hbad, mul_zero]
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

theorem native_graph_constant_word_rate_eq_of_independent (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    nativeSignedGeneralWordRate G G (fun _ => true) (fun _ => true) +
      nativeSignedGeneralWordRate G G (fun _ => false) (fun _ => false) =
        (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEvenCycleCount P G : Real)) := by
  let f := fun O T : Finset (Prod Nat Nat) =>
    (1 + (-1 : Real) ^ (O.card + T.card)) *
      numeratorPrincipalIndicator (nativeSignedRowProduct O T)
  have hi : forall O : Finset (Prod Nat Nat), Membership.mem G.powerset O ->
      G.powerset.sum (fun T => f O T) = f O O := by
    intro O hO
    apply Finset.sum_eq_single O
    . intro T hT hne
      have hbad : Not (nativeSignedCycleMask P O T) := fun h => hne h.1.symm
      have hz := native_graph_noncycle_indicator_eq_zero P hP hind O T
        ((Finset.mem_powerset.mp hO).trans hG) ((Finset.mem_powerset.mp hT).trans hG) hbad
      change (1 + (-1 : Real) ^ (O.card + T.card)) *
        numeratorPrincipalIndicator (nativeSignedRowProduct O T) = 0
      rw [hz, mul_zero]
    . intro hn
      exact False.elim (hn hO)
  have hsub : nativeEvenCycleMasks P G <= G.powerset := Finset.filter_subset _ _
  have ho : forall C : Finset (Prod Nat Nat), Membership.mem G.powerset C ->
      Not (Membership.mem (nativeEvenCycleMasks P G) C) -> f C C = 0 := by
    intro C hC hn
    have hCG := Finset.mem_powerset.mp hC
    have hs := hCG.trans hG
    have hbad : Not (nativeSignedCycleMask P C C) := by
      intro h
      exact hn ((native_even_cycle_masks_mem_iff P G C).mpr (And.intro hCG h.2))
    have hz := native_graph_noncycle_indicator_eq_zero P hP hind C C hs hs hbad
    change (1 + (-1 : Real) ^ (C.card + C.card)) *
      numeratorPrincipalIndicator (nativeSignedRowProduct C C) = 0
    rw [hz, mul_zero]
  have hm : (nativeEvenCycleMasks P G).sum (fun C => f C C) =
      2 * (nativeEvenCycleCount P G : Real) := by
    calc
      _ = (nativeEvenCycleMasks P G).sum (fun _ => (2 : Real)) := by
        apply Finset.sum_congr rfl
        intro C hC
        exact native_graph_paired_mask_eq_two_of_cycle P hP G hG C hC
      _ = (nativeEvenCycleCount P G : Real) * 2 := by simp [nativeEvenCycleCount]
      _ = _ := mul_comm _ _
  have hall : G.powerset.sum (fun O => G.powerset.sum (fun T => f O T)) =
      2 * (nativeEvenCycleCount P G : Real) := by
    calc
      _ = G.powerset.sum (fun O => f O O) := Finset.sum_congr rfl hi
      _ = (nativeEvenCycleMasks P G).sum (fun C => f C C) :=
        (Finset.sum_subset hsub ho).symm
      _ = _ := hm
  rw [native_graph_constant_word_sum_expansion]
  change (1 / (2 : Real) ^ (G.card + G.card)) *
      G.powerset.sum (fun O => G.powerset.sum (fun T => f O T)) =
    (1 / (2 : Real) ^ (G.card + G.card)) * (2 * (nativeEvenCycleCount P G : Real))
  rw [hall]

theorem native_graph_agreement_rate_eq_of_independent (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    nativeGraphAgreementRate G =
      (nativeEvenCycleCount P G : Real) *
        (1 / (2 : Real) ^ G.card + 2 / (2 : Real) ^ (G.card + G.card)) := by
  unfold nativeGraphAgreementRate
  rw [add_assoc, native_graph_constant_word_rate_eq_of_independent P hP hind G hG,
    native_graph_zero_rate_eq_of_independent P hP hind G hG]
  ring

theorem native_reservoir_graph_agreement_ratio_tendsto
    (R : Nat -> Prop) [DecidablePred R] (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p ->
      Membership.mem (nativePrimeVertexGapReservoirClass R) p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) :
    Tendsto (fun U : Nat =>
      nativeGraphAgreementMass G (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds ((nativeEvenCycleCount P G : Real) *
        (1 / (2 : Real) ^ G.card + 2 / (2 : Real) ^ (G.card + G.card)))) := by
  have hp : forall p : Nat, Membership.mem P p -> Nat.Prime p :=
    fun p hm => (native_gap_reservoir_class_geometry R p (hP p hm)).1
  have hind := native_gap_reservoir_class_finite_independent R P hP
  rw [<- native_graph_agreement_rate_eq_of_independent P hp hind G hG]
  exact native_graph_agreement_ratio_tendsto P hp G hG hne

theorem native_infinite_graph_coincidence_family_in_reservoir
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
              nativeGraphAgreementMass G (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
                reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
              atTop (nhds ((nativeEvenCycleCount P G : Real) *
                (1 / (2 : Real) ^ G.card + 2 / (2 : Real) ^ (G.card + G.card)))))) := by
  have h := native_infinite_prime_gap_independent_family_in_reservoir R hR
  exact And.intro h.1 (And.intro h.2.1 (native_reservoir_graph_agreement_ratio_tendsto R))

theorem native_infinite_graph_coincidence_family :
    And (Set.Infinite (nativePrimeVertexGapReservoirClass (fun _ => True)))
      (And (forall p : Nat,
          Membership.mem (nativePrimeVertexGapReservoirClass (fun _ => True)) p -> Nat.Prime p)
        (forall P : Finset Nat,
          (forall p : Nat, Membership.mem P p ->
            Membership.mem (nativePrimeVertexGapReservoirClass (fun _ => True)) p) ->
          forall G : Finset (Prod Nat Nat), G <= nativePrimeVertexEdges P -> G.Nonempty ->
            Tendsto (fun U : Nat =>
              nativeGraphAgreementMass G (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
                reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
              atTop (nhds ((nativeEvenCycleCount P G : Real) *
                (1 / (2 : Real) ^ G.card + 2 / (2 : Real) ^ (G.card + G.card)))))) := by
  have h := native_infinite_prime_gap_independent_family
  exact And.intro h.1 (And.intro h.2.1
    (native_reservoir_graph_agreement_ratio_tendsto (fun _ => True)))

end PrimeFactorOscillations.FiniteFieldIntegerSignature
