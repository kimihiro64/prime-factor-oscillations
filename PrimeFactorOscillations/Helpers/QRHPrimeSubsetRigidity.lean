/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimeSquarefreeGlobalSpectrum

/-! # Extremal density and parity rigidity for squarefree prime differences -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Filter
open scoped Classical
namespace PrimeFactorOscillations.QRH

def primeSubsetDensity (X : Nat) (B : Finset Nat) : Real :=
  (B.card : Real) / ((oddPrimeVertices X).card : Real)

def primeSubsetBias (X : Nat) (B : Finset Nat) : Real :=
  B.sum primeResidueSign / ((oddPrimeVertices X).card : Real)

def primeResidueClass (X r : Nat) : Finset Nat :=
  (oddPrimeVertices X).filter (fun p => (p : ZMod 4) = (r : ZMod 4))

def primeSubsetParityDistance (X : Nat) (B : Finset Nat) : Real :=
  min (((symmDiff B (primeResidueClass X 1)).card : Real) /
      ((oddPrimeVertices X).card : Real))
    (((symmDiff B (primeResidueClass X 3)).card : Real) /
      ((oddPrimeVertices X).card : Real))

def SquarefreeDifferenceIndependent (B : Finset Nat) : Prop :=
  forall p, Membership.mem B p -> forall q, Membership.mem B q ->
    Not (p = q) -> Not (Squarefree ((q : Int) - (p : Int)).natAbs)

private theorem vertex_count_pos {X : Nat} (hX : 3 <= X) :
    (0 : Real) < (oddPrimeVertices X).card := by
  apply Nat.cast_pos.mpr
  apply Finset.card_pos.mpr
  refine Exists.intro 3 ?_
  exact Finset.mem_erase.mpr (And.intro (by decide)
    (Nat.mem_primesBelow.mpr (And.intro (by omega) Nat.prime_three)))

private theorem sum_mask (S B : Finset Nat) (hB : B <= S) (g : Nat -> Real) :
    S.sum (fun p => if Membership.mem B p then g p else 0) = B.sum g := by
  calc
    _ = B.sum (fun p => if Membership.mem B p then g p else 0) := by
      symm
      apply Finset.sum_subset hB
      intro p hpS hpB
      simp [hpB]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hpB
      simp [hpB]

private theorem independent_mask_zero (X : Nat) (B : Finset Nat)
    (hB : SquarefreeDifferenceIndependent B) :
    Finset.kernelBilinear (oddPrimeVertices X) primeSquarefreeDifferenceKernel
      (fun p => if Membership.mem B p then 1 else 0)
      (fun p => if Membership.mem B p then 1 else 0) = 0 := by
  unfold Finset.kernelBilinear
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hpB : Membership.mem B p
  { by_cases hqB : Membership.mem B q
    { by_cases hpq : p = q
      { subst q
        simp [primeSquarefreeDifferenceKernel] }
      { simp [primeSquarefreeDifferenceKernel, hB p hpB q hqB hpq] } }
    { simp [hqB] } }
  { simp [hpB] }

private theorem vertex_residues (X p : Nat) (hp : Membership.mem (oddPrimeVertices X) p) :
    Or ((p : ZMod 4) = 1) ((p : ZMod 4) = 3) := by
  have hm := Finset.mem_erase.mp hp
  have hpPrime := (Nat.mem_primesBelow.mp hm.2).2
  have hi : IsUnit (p : ZMod 4) := by
    simpa only [Nat.reducePow] using
      prime_square_residue_isUnit p 2 hpPrime Nat.prime_two hm.1
  choose u hu using hi
  have hv := ZMod.unitsFourEquivBool_symm_val (ZMod.unitsFourEquivBool u)
  rw [Equiv.symm_apply_apply] at hv
  cases hb : ZMod.unitsFourEquivBool u with
  | false =>
    left
    exact hu.symm.trans (by simpa only [hb, Bool.false_eq_true, ite_false] using hv)
  | true =>
    right
    exact hu.symm.trans (by simpa only [hb, ite_true] using hv)

private theorem symmetric_difference_card (S B C : Finset Nat)
    (hB : B <= S) (hC : C <= S) :
    ((symmDiff B C).card : Real) =
      S.sum (fun p => if Membership.mem B p then
        (if Membership.mem C p then 0 else 1)
        else (if Membership.mem C p then 1 else 0)) := by
  have hSub : symmDiff B C <= S := by
    intro p hp
    have h := hp
    simp [symmDiff] at h
    cases h with
    | inl h => exact hB h.1
    | inr h => exact hC h.1
  have hSum : S.sum (fun p => if Membership.mem (symmDiff B C) p then
      (1 : Real) else 0) = ((symmDiff B C).card : Real) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      sum_mask S (symmDiff B C) hSub (fun _ => (1 : Real))
  rw [<- hSum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hb : Membership.mem B p <;>
    by_cases hc : Membership.mem C p <;> simp [symmDiff, hb, hc]

private theorem residue_class_difference_cards (X : Nat) (B : Finset Nat)
    (hB : B <= oddPrimeVertices X) :
    And
      (((symmDiff B (primeResidueClass X 1)).card : Real) =
        ((oddPrimeVertices X).card : Real) / 2 +
          (oddPrimeVertices X).sum primeResidueSign / 2 - B.sum primeResidueSign)
      (((symmDiff B (primeResidueClass X 3)).card : Real) =
        ((oddPrimeVertices X).card : Real) / 2 -
          (oddPrimeVertices X).sum primeResidueSign / 2 + B.sum primeResidueSign) := by
  have h31 : Not ((3 : ZMod 4) = 1) := by decide
  have h13 : Not ((1 : ZMod 4) = 3) := by decide
  constructor
  { rw [symmetric_difference_card (oddPrimeVertices X) B (primeResidueClass X 1)
      hB (Finset.filter_subset _ _)]
    calc
      _ = (oddPrimeVertices X).sum (fun p => (1 + primeResidueSign p) / 2 -
          (if Membership.mem B p then primeResidueSign p else 0)) := by
        apply Finset.sum_congr rfl
        intro p hp
        cases vertex_residues X p hp with
        | inl h => by_cases hb : Membership.mem B p <;>
            norm_num [primeResidueClass, primeResidueSign, hp, h, hb, h31, h13]
        | inr h => by_cases hb : Membership.mem B p <;>
            norm_num [primeResidueClass, primeResidueSign, hp, h, hb, h31, h13]
      _ = _ := by
        rw [Finset.sum_sub_distrib, <- Finset.sum_div, Finset.sum_add_distrib,
          sum_mask _ _ hB]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        ring1 }
  { rw [symmetric_difference_card (oddPrimeVertices X) B (primeResidueClass X 3)
      hB (Finset.filter_subset _ _)]
    calc
      _ = (oddPrimeVertices X).sum (fun p => (1 - primeResidueSign p) / 2 +
          (if Membership.mem B p then primeResidueSign p else 0)) := by
        apply Finset.sum_congr rfl
        intro p hp
        cases vertex_residues X p hp with
        | inl h => by_cases hb : Membership.mem B p <;>
            norm_num [primeResidueClass, primeResidueSign, hp, h, hb, h31, h13]
        | inr h => by_cases hb : Membership.mem B p <;>
            norm_num [primeResidueClass, primeResidueSign, hp, h, hb, h31, h13]
      _ = _ := by
        rw [Finset.sum_add_distrib, <- Finset.sum_div, Finset.sum_sub_distrib,
          sum_mask _ _ hB]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        ring1 }

private theorem scalar_stability (a b mu delta tau d : Real)
    (ht : 0 <= tau) (hd : delta <= tau ^ 2)
    (hRow : 6 * a ^ 2 - 4 * b ^ 2 <= a + delta)
    (hMu : abs mu <= tau)
    (hDist : d = 1 / 2 - abs (b - mu / 2)) :
    d <= 1 / 2 - Real.sqrt (6 * a ^ 2 - a) / 2 + tau := by
  have hCross : 0 <= abs b * tau := mul_nonneg (abs_nonneg _) ht
  have hRoot : Real.sqrt (6 * a ^ 2 - a) <= 2 * abs b + tau := by
    apply Real.sqrt_le_iff.mpr
    constructor
    { positivity }
    { nlinarith only [hRow, hd, hCross, sq_abs b] }
  have hAbs := abs_sub_abs_le_abs_sub b (mu / 2)
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : Real) <= 2)] at hAbs
  rw [hDist]
  linarith only [hRoot, hAbs, hMu]


private theorem parity_distance_identity (X : Nat) (B : Finset Nat)
    (hX : 3 <= X) (hB : B <= oddPrimeVertices X) :
    primeSubsetParityDistance X B = 1 / 2 -
      abs (primeSubsetBias X B -
        (oddPrimeVertices X).sum primeResidueSign /
          ((oddPrimeVertices X).card : Real) / 2) := by
  have hn := vertex_count_pos hX
  have h := residue_class_difference_cards X B hB
  unfold primeSubsetParityDistance
  rw [h.1, h.2]
  let n : Real := (oddPrimeVertices X).card
  let m : Real := (oddPrimeVertices X).sum primeResidueSign / n
  let b : Real := primeSubsetBias X B
  have hp : (n / 2 + (oddPrimeVertices X).sum primeResidueSign / 2 -
      B.sum primeResidueSign) / n = 1 / 2 + m / 2 - b := by
    dsimp [n, m, b, primeSubsetBias]
    field_simp [hn.ne']
  have hm : (n / 2 - (oddPrimeVertices X).sum primeResidueSign / 2 +
      B.sum primeResidueSign) / n = 1 / 2 - m / 2 + b := by
    dsimp [n, m, b, primeSubsetBias]
    field_simp [hn.ne']
  change min ((n / 2 + _ / 2 - _) / n) ((n / 2 - _ / 2 + _) / n) =
    1 / 2 - abs (b - m / 2)
  rw [hp, hm]
  by_cases hb : 0 <= b - m / 2
  { rw [abs_of_nonneg hb, min_eq_left (by linarith)]
    ring1 }
  { rw [abs_of_nonpos (le_of_not_ge hb), min_eq_right (by linarith)]
    ring1 }

private theorem subset_statistics (X : Nat) (B : Finset Nat)
    (hX : 3 <= X) (hB : B <= oddPrimeVertices X) :
    And (0 <= primeSubsetDensity X B)
      (And (primeSubsetDensity X B <= 1)
        (abs (primeSubsetBias X B) <= primeSubsetDensity X B)) := by
  have hn := vertex_count_pos hX
  have hCard : (B.card : Real) <= (oddPrimeVertices X).card :=
    Nat.cast_le.mpr (Finset.card_le_card hB)
  have ha : 0 <= primeSubsetDensity X B :=
    div_nonneg (Nat.cast_nonneg _) hn.le
  have ha1 : primeSubsetDensity X B <= 1 := (div_le_one hn).mpr hCard
  refine And.intro ha (And.intro ha1 ?_)
  unfold primeSubsetBias primeSubsetDensity
  rw [abs_div, abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  calc
    abs (B.sum primeResidueSign) <= B.sum (fun p => abs (primeResidueSign p)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = B.sum (fun _ => (1 : Real)) := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold primeResidueSign
      split_ifs <;> norm_num
    _ = (B.card : Real) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The full spectral estimate itself forces asymptotic balance of the two parity modes. -/
theorem eventually_prime_parity_balance {eps : Real} (heps : 0 < eps) :
    Filter.Eventually (fun X : Nat =>
      abs ((oddPrimeVertices X).sum primeResidueSign /
        ((oddPrimeVertices X).card : Real)) <= eps) atTop := by
  have hEta : (0 : Real) < eps ^ 2 / 20 := by positivity
  have hSpec := eventually_prime_squarefree_spectral_gap hEta
  filter_upwards [hSpec, eventually_ge_atTop (3 : Nat)] with X hS hX
  have hn := vertex_count_pos hX
  have h := hS (fun _ => (1 : Real))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_pow, div_self hn.ne'] at h
  let A := artinPrimeSquareConstant
  let m := (oddPrimeVertices X).sum primeResidueSign /
    ((oddPrimeVertices X).card : Real)
  have hNonneg := (abs_nonneg _).trans h
  have hA : (1 / 4 : Real) <= A := artinPrimeSquareConstant_bounds.1
  have hCorrection := mul_nonneg (sub_nonneg.mpr hA) (sq_nonneg m)
  have hSquare : m ^ 2 <= eps ^ 2 := by
    change 0 <= A / 5 * (1 - 1 - m ^ 2) + eps ^ 2 / 20 at hNonneg
    nlinarith only [hNonneg, hCorrection]
  change abs m <= eps
  nlinarith only [hSquare, sq_abs m, abs_nonneg m, heps]


/-- Every single residue class modulo four has no squarefree difference. -/
theorem prime_residue_class_independent (X r : Nat) :
    SquarefreeDifferenceIndependent (primeResidueClass X r) := by
  intro p hp q hq hpq
  have hCast : (p : ZMod 4) = (q : ZMod 4) :=
    (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  have hBad : Not (forall ell : Nat, Nat.Prime ell ->
      Not ((p : ZMod (ell ^ 2)) = (q : ZMod (ell ^ 2)))) := by
    intro h
    apply h 2 Nat.prime_two
    simpa only [Nat.reducePow] using hCast
  intro hSquare
  have hK : primeSquarefreeDifferenceKernel p q = 1 := by
    simp [primeSquarefreeDifferenceKernel, hSquare]
  rw [primeSquarefreeDifferenceKernel_eq_prime_avoidance] at hK
  simp [hBad] at hK

/-- The two actual parity-class constructions both attain density one half. -/
theorem eventually_prime_parity_class_densities {eps : Real} (heps : 0 < eps) :
    Filter.Eventually (fun X : Nat =>
      And (abs (primeSubsetDensity X (primeResidueClass X 1) - 1 / 2) <= eps)
        (abs (primeSubsetDensity X (primeResidueClass X 3) - 1 / 2) <= eps)) atTop := by
  filter_upwards [eventually_prime_parity_balance heps,
    eventually_ge_atTop (3 : Nat)] with X hBalance hX
  have hn := vertex_count_pos hX
  have hc := residue_class_difference_cards X ({} : Finset Nat) (Finset.empty_subset _)
  have hp : ((primeResidueClass X 1).card : Real) =
      ((oddPrimeVertices X).card : Real) / 2 +
        (oddPrimeVertices X).sum primeResidueSign / 2 := by
    simpa [symmDiff] using hc.1
  have hm : ((primeResidueClass X 3).card : Real) =
      ((oddPrimeVertices X).card : Real) / 2 -
        (oddPrimeVertices X).sum primeResidueSign / 2 := by
    simpa [symmDiff] using hc.2
  have hpNorm : primeSubsetDensity X (primeResidueClass X 1) - 1 / 2 =
      (oddPrimeVertices X).sum primeResidueSign /
        ((oddPrimeVertices X).card : Real) / 2 := by
    unfold primeSubsetDensity
    rw [hp]
    field_simp [hn.ne']
    ring1
  have hmNorm : primeSubsetDensity X (primeResidueClass X 3) - 1 / 2 =
      -((oddPrimeVertices X).sum primeResidueSign /
        ((oddPrimeVertices X).card : Real) / 2) := by
    unfold primeSubsetDensity
    rw [hm]
    field_simp [hn.ne']
    ring1
  constructor
  { rw [hpNorm, abs_div, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    linarith only [hBalance, heps] }
  { rw [hmNorm, abs_neg, abs_div, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    linarith only [hBalance, heps] }

/-- Uniform extremal density and quantitative parity rigidity for actual prime subsets. -/
theorem eventually_squarefree_independent_prime_subset_bounds {eps : Real} (heps : 0 < eps) :
    Filter.Eventually (fun X : Nat => forall B : Finset Nat,
      B <= oddPrimeVertices X -> SquarefreeDifferenceIndependent B ->
      And (6 * (primeSubsetDensity X B) ^ 2 - 4 * (primeSubsetBias X B) ^ 2 <=
        primeSubsetDensity X B + eps)
        (And (primeSubsetDensity X B <= 1 / 2 + eps)
          (primeSubsetParityDistance X B <= 1 / 2 -
            Real.sqrt (6 * (primeSubsetDensity X B) ^ 2 - primeSubsetDensity X B) / 2 +
              eps))) atTop := by
  let eta : Real := min eps (eps ^ 2) / 20
  have hEta : 0 < eta := by dsimp [eta]; positivity
  have hBudget : 20 * eta <= eps := by
    dsimp [eta]
    nlinarith only [min_le_left eps (eps ^ 2)]
  have hBudgetSq : 20 * eta <= eps ^ 2 := by
    dsimp [eta]
    nlinarith only [min_le_right eps (eps ^ 2)]
  filter_upwards [eventually_prime_squarefree_spectral_gap hEta,
    eventually_prime_parity_balance heps, eventually_ge_atTop (3 : Nat)] with X hS hMu hX
  intro B hB hIndependent
  let S := oddPrimeVertices X
  let n : Real := S.card
  let A := artinPrimeSquareConstant
  let a := primeSubsetDensity X B
  let b := primeSubsetBias X B
  let m := S.sum primeResidueSign / n
  let f : Nat -> Real := fun p => if Membership.mem B p then 1 else 0
  have hStats := subset_statistics X B hX hB
  have hA : S.sum f = (B.card : Real) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      sum_mask S B hB (fun _ => (1 : Real))
  have hBMean : S.sum (fun p => primeResidueSign p * f p) = B.sum primeResidueSign := by
    calc
      _ = S.sum (fun p => if Membership.mem B p then primeResidueSign p else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hb : Membership.mem B p <;> simp [f, hb]
      _ = _ := sum_mask S B hB primeResidueSign
  have hEnergy : S.sum (fun p => (f p) ^ 2) = (B.card : Real) := by
    calc
      _ = S.sum f := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hb : Membership.mem B p <;> simp [f, hb]
      _ = _ := hA
  have hQ : Finset.kernelBilinear S primeSquarefreeDifferenceKernel f f = 0 :=
    independent_mask_zero X B hIndependent
  have h := hS f
  change abs (Finset.kernelBilinear S primeSquarefreeDifferenceKernel f f / n ^ 2 -
      A * ((S.sum f / n) ^ 2 -
        (S.sum (fun p => primeResidueSign p * f p) / n) ^ 2)) <=
    A / 5 * (S.sum (fun p => (f p) ^ 2) / n - (S.sum f / n) ^ 2 -
      (S.sum (fun p => primeResidueSign p * f p) / n) ^ 2) +
        eta * (S.sum (fun p => (f p) ^ 2) / n) at h
  rw [hA, hBMean, hEnergy, hQ, zero_div, zero_sub, abs_neg] at h
  change abs (A * (a ^ 2 - b ^ 2)) <= A / 5 * (a - a ^ 2 - b ^ 2) + eta * a at h
  have hLower := (le_abs_self (A * (a ^ 2 - b ^ 2))).trans h
  have hRow : 6 * a ^ 2 - 4 * b ^ 2 <= a + 20 * eta := by
    by_cases hEasy : 6 * a ^ 2 - 4 * b ^ 2 <= a
    { linarith only [hEasy, hEta] }
    have hDeficit : 0 <= 6 * a ^ 2 - 4 * b ^ 2 - a := by linarith only [hEasy]
    have hCorrection := mul_nonneg
      (sub_nonneg.mpr artinPrimeSquareConstant_bounds.1) hDeficit
    have hMass := mul_nonneg hEta.le (sub_nonneg.mpr hStats.2.1)
    change 0 <= (A - 1 / 4) * (6 * a ^ 2 - 4 * b ^ 2 - a) at hCorrection
    change 0 <= eta * (1 - a) at hMass
    nlinarith only [hLower, hCorrection, hMass]
  have hBetaSquare : b ^ 2 <= a ^ 2 := by
    have hProduct := mul_nonneg (sub_nonneg.mpr hStats.2.2)
      (add_nonneg hStats.1 (abs_nonneg b))
    change 0 <= (a - abs b) * (a + abs b) at hProduct
    nlinarith only [hProduct, sq_abs b]
  refine And.intro (by change 6 * a ^ 2 - 4 * b ^ 2 <= a + eps; linarith only [hRow, hBudget])
    (And.intro ?_ ?_)
  { change a <= 1 / 2 + eps
    nlinarith only [hRow, hBetaSquare, hBudget, sq_nonneg (a - 1 / 2)] }
  { exact scalar_stability a b m (20 * eta) eps (primeSubsetParityDistance X B)
      heps.le hBudgetSq hRow hMu (parity_distance_identity X B hX hB) }

end PrimeFactorOscillations.QRH
