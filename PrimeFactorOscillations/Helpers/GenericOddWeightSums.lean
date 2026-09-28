import PrimeFactorOscillations.Definitions.WeightSums
import PrimeFactorOscillations.Helpers.GenericOddWeights

set_option autoImplicit false

/-!
# Uniform transfer of the prime-prefix odds sum

The two laws have the same leading weight-sum term up to an explicit bounded
error. The exceptional prime 2 contributes one; all later corrections fit
inside a telescoping reciprocal sum. Every statement is uniform in the cutoff.
-/

namespace PrimeFactorOscillations

/-- Normalize the dependency's natural-subtraction weight on its valid domain. -/
theorem ordinaryWeight_cast (p : Nat) (hp : 1 <= p) :
    PrimeFactorUnimodality.primeWeight p = 1 / ((p : Rat) - 1) := by
  simp only [PrimeFactorUnimodality.primeWeight, Nat.cast_sub hp, Nat.cast_one]

/-- A correction bound whose right side telescopes over consecutive integers. -/
theorem genericOdd_correction_le_telescope (p : Nat) (hp : 2 < p) :
    PrimeFactorUnimodality.primeWeight p - genericOddWeight p <=
      2 / ((p : Rat) - 1) - 2 / (p : Rat) := by
  have hpR : (2 : Rat) < (p : Rat) := by exact_mod_cast hp
  have hp0 : Not ((p : Rat) = 0) := by linarith
  have hp1 : Not ((p : Rat) - 1 = 0) := by linarith
  rw [ordinaryWeight_cast p (by omega), genericOddWeight]
  calc
    1 / ((p : Rat) - 1) - genericOddEta p / (1 - genericOddEta p) <=
        2 / (p : Rat) ^ 2 := genericOdd_weight_correction_le p hp
    _ <= 2 / ((p : Rat) * ((p : Rat) - 1)) :=
      div_le_div_of_nonneg_left (by norm_num)
        (mul_pos (by linarith) (by linarith)) (by nlinarith)
    _ = 2 / ((p : Rat) - 1) - 2 / (p : Rat) := by
      field_simp
      ring

/-- Express the difference on one common finite support, including all exceptions. -/
theorem primeWeightSum_difference_eq (x : Nat) :
    ordinaryPrimeWeightSum x - genericOddPrimeWeightSum x =
      (Finset.range x).sum (fun p => if Nat.Prime p then
        PrimeFactorUnimodality.primeWeight p - genericOddWeight p else 0) := by
  unfold ordinaryPrimeWeightSum genericOddPrimeWeightSum
  rw [<- Finset.sum_sub_distrib, Finset.sum_filter]

/-- Exact successor recursion for the weight-sum difference. -/
theorem primeWeightSum_difference_succ (x : Nat) :
    ordinaryPrimeWeightSum (x + 1) - genericOddPrimeWeightSum (x + 1) =
      ordinaryPrimeWeightSum x - genericOddPrimeWeightSum x +
        (if Nat.Prime x then PrimeFactorUnimodality.primeWeight x - genericOddWeight x
          else 0) := by
  rw [primeWeightSum_difference_eq, Finset.sum_range_succ, <- primeWeightSum_difference_eq]

/-- The ordinary weight sum dominates the generic odd weight sum. -/
theorem genericOdd_weightSum_difference_nonneg (x : Nat) :
    0 <= ordinaryPrimeWeightSum x - genericOddPrimeWeightSum x := by
  rw [primeWeightSum_difference_eq]
  apply Finset.sum_nonneg
  intro p hp
  by_cases hprime : Nat.Prime p
  next =>
    rw [ite_eq_left hprime]
    by_cases htwo : p = 2
    next =>
      subst p
      norm_num [PrimeFactorUnimodality.primeWeight, genericOddWeight, genericOddEta]
    next =>
      have hp2 := hprime.two_le
      have hpgt : 2 < p := by omega
      rw [ordinaryWeight_cast p (by omega), genericOddWeight]
      exact le_of_lt (genericOdd_weight_correction_bound p hpgt).1
  next =>
    simp only [ite_eq_right hprime, le_refl]

/-- Explicit envelope after the exceptional prime 2. -/
theorem genericOdd_weightSum_envelope (n : Nat) (hn : 2 <= n) :
    ordinaryPrimeWeightSum (n + 1) - genericOddPrimeWeightSum (n + 1) <=
      2 - 2 / (n : Rat) := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num [ordinaryPrimeWeightSum, genericOddPrimeWeightSum, Finset.sum_filter,
        Finset.sum_range_succ, PrimeFactorUnimodality.primeWeight, genericOddWeight,
        genericOddEta, Nat.prime_two, Nat.not_prime_zero, Nat.not_prime_one]
  | succ n hn ih =>
      rw [primeWeightSum_difference_succ (n + 1)]
      have hnR : (0 : Rat) < (n : Rat) := by exact_mod_cast (show 0 < n by omega)
      have hterm :
          (if Nat.Prime (n + 1) then
            PrimeFactorUnimodality.primeWeight (n + 1) - genericOddWeight (n + 1) else 0) <=
          2 / (n : Rat) - 2 / ((n + 1 : Nat) : Rat) := by
        by_cases hp : Nat.Prime (n + 1)
        next =>
          rw [ite_eq_left hp]
          simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
            genericOdd_correction_le_telescope (n + 1) (by omega)
        next =>
          rw [ite_eq_right hp]
          apply sub_nonneg.mpr
          apply div_le_div_of_nonneg_left (by norm_num) hnR
          simp only [Nat.cast_add, Nat.cast_one]
          linarith
      linarith

/-- Uniform bounded-error transfer for every natural prime cutoff. -/
theorem genericOdd_weightSum_transfer (x : Nat) :
    0 <= ordinaryPrimeWeightSum x - genericOddPrimeWeightSum x /\
      ordinaryPrimeWeightSum x - genericOddPrimeWeightSum x <= 2 := by
  refine And.intro (genericOdd_weightSum_difference_nonneg x) ?_
  by_cases hx : 3 <= x
  next =>
    have h := genericOdd_weightSum_envelope (x - 1) (by omega)
    rw [Nat.sub_add_cancel (show 1 <= x by omega)] at h
    exact le_trans h (sub_le_self _ (div_nonneg (by norm_num) (Nat.cast_nonneg _)))
  next =>
    have hcases : x = 0 \/ x = 1 \/ x = 2 := by omega
    rcases hcases with h | h | h <;> subst x <;>
      norm_num [ordinaryPrimeWeightSum, genericOddPrimeWeightSum, Finset.sum_filter,
        Finset.sum_range_succ, PrimeFactorUnimodality.primeWeight, genericOddWeight,
        genericOddEta, Nat.prime_two, Nat.not_prime_zero, Nat.not_prime_one]

end PrimeFactorOscillations
