/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingUniform

/-!
# Arbitrary coefficient partial sums of the actual sampling error

The explicit signed floor-error polynomial has no coefficients above the
finite prime-support size. Consequently its complete budget controls every
partial sum, including ranks larger than the moving prime cutoff. This is
the finite-sum input for the infinite coefficient law.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.PrimeClassDecoder

theorem finiteSamplingError_coeff_eq_zero_of_card_lt
    (s : Finset Nat) (N k : Nat) (hk : s.card < k) :
    (finiteSamplingErrorPolynomial s N).coeff k = 0 := by
  classical
  unfold finiteSamplingErrorPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro t ht
  rw [Polynomial.coeff_C_mul]
  have htk : t.card < k :=
    lt_of_le_of_lt (Finset.card_le_card (Finset.mem_powerset.mp ht)) hk
  have hzero : ((Polynomial.X - 1 : Polynomial Real) ^ t.card).coeff k = 0 := by
    apply abs_eq_zero.mp
    rw [abs_coeff_X_sub_one_pow, Nat.choose_eq_zero_of_lt htk, Nat.cast_zero]
  rw [hzero, mul_zero]

theorem sum_range_abs_le_of_zero_tail
    (f : Nat -> Real) (L K : Nat)
    (hzero : forall k, L <= k -> f k = 0) :
    (Finset.range K).sum (fun k => abs (f k)) <=
      (Finset.range L).sum (fun k => abs (f k)) := by
  cases le_total K L with
  | inl hKL =>
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hKL)
      intro k hk hnot
      exact abs_nonneg _
  | inr hLK =>
      have heq :
          (Finset.range L).sum (fun k => abs (f k)) =
            (Finset.range K).sum (fun k => abs (f k)) := by
        apply Finset.sum_subset (Finset.range_mono hLK)
        intro k hk hnot
        have hLk : L <= k :=
          Nat.le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h))
        rw [hzero k hLk, abs_zero]
      exact le_of_eq heq.symm

theorem actualSample_difference_eq_error_coeff
    (P : Set Nat) (N Y k : Nat) (hNY : N <= Y) :
    (sampleCount P N k : Real) / (N : Real) -
        (finiteReferencePolynomial (primeClassPrefix P Y)).coeff k =
      (finiteSamplingErrorPolynomial (primeClassPrefix P Y) N).coeff k := by
  have heq := congrArg (fun f : Polynomial Real => f.coeff k)
    (finiteEmpirical_sub_reference_eq_error (primeClassPrefix P Y)
      (fun p hp => primeClassPrefix_prime P Y p hp) N)
  simpa only [Polynomial.coeff_sub,
    coeff_finiteEmpirical_primeClassPrefix P N Y k hNY] using heq

theorem actualSample_partial_coefficient_error_le_exp
    (P : Set Nat) (N Y K : Nat) (hNY : N <= Y) (hN : 0 < N)
    (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    (Finset.range K).sum (fun k =>
      abs ((sampleCount P N k : Real) / (N : Real) -
        (finiteReferencePolynomial (primeClassPrefix P Y)).coeff k)) <=
      (N : Real) ^ (sigma - 1) * Real.exp (2 * tsum (classPowerWeight P sigma)) := by
  apply le_trans (sum_range_abs_le_of_zero_tail
    (fun k => (sampleCount P N k : Real) / (N : Real) -
      (finiteReferencePolynomial (primeClassPrefix P Y)).coeff k)
    ((primeClassPrefix P Y).card + 1) K ?_)
    (actualSample_coefficient_error_le_exp P N Y hNY hN sigma hs0 hs1 hsum)
  intro k hk
  rw [actualSample_difference_eq_error_coeff P N Y k hNY]
  exact finiteSamplingError_coeff_eq_zero_of_card_lt _ N k (by omega)

theorem actualSample_single_coefficient_error_le_exp
    (P : Set Nat) (N Y k : Nat) (hNY : N <= Y) (hN : 0 < N)
    (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    abs ((sampleCount P N k : Real) / (N : Real) -
      (finiteReferencePolynomial (primeClassPrefix P Y)).coeff k) <=
      (N : Real) ^ (sigma - 1) * Real.exp (2 * tsum (classPowerWeight P sigma)) := by
  apply le_trans (Finset.single_le_sum
    (fun j hj => abs_nonneg ((sampleCount P N j : Real) / (N : Real) -
      (finiteReferencePolynomial (primeClassPrefix P Y)).coeff j))
    (Finset.mem_range.mpr (Nat.lt_succ_self k)))
  exact actualSample_partial_coefficient_error_le_exp
    P N Y (k + 1) hNY hN sigma hs0 hs1 hsum

end PrimeFactorOscillations.PrimeClassSampling
