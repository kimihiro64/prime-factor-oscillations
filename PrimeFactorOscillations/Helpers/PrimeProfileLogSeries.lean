/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import PrimeFactorOscillations.Helpers.PrimeProfilePositive
import PrimeFactorOscillations.Helpers.PrimeProfileTail

/-!
# Exact logarithmic prime-profile tails

The logarithmic factors are absolutely summable. Their sum is the logarithm
of the actual positive entire profile. The tail uses exactly the primes
strictly above the inclusive cutoff, and its sign follows from Bernoulli's
inequalities for real exponents.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter

theorem summable_primeProfile_logFactor (z : Real) (hz : 0 <= z) :
    Summable (fun p : Nat.Primes =>
      Real.log (1 + primeProfileWeight (p : Nat) * z) -
        Real.log (1 + primeProfileWeight (p : Nat)) * z) := by
  apply (summable_primeProfileWeight_sq.mul_left ((z ^ 2 + z) / 2)).of_norm_bounded
  intro p
  let a := primeProfileWeight (p : Nat)
  have ha : 0 <= a := primeProfileWeight_nonneg _
  have hOne := Real.sub_log_one_add_bounds (a * z) (mul_nonneg ha hz)
  have hTwo := Real.sub_log_one_add_bounds a ha
  have hLower := mul_nonneg hz hTwo.1
  have hUpper := mul_le_mul_of_nonneg_left hTwo.2 hz
  have hPositiveLinear : 0 <= z * a ^ 2 := mul_nonneg hz (sq_nonneg a)
  have hPositiveSquare : 0 <= z ^ 2 * a ^ 2 := mul_nonneg (sq_nonneg z) (sq_nonneg a)
  change norm (Real.log (1 + a * z) - Real.log (1 + a) * z) <=
    ((z ^ 2 + z) / 2) * a ^ 2
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  . nlinarith only [hOne.2, hLower, hPositiveLinear]
  . nlinarith only [hOne.1, hUpper, hPositiveSquare]

theorem log_primeProfile_eq_tsum (z : Real) (hz : 0 <= z) :
    Real.log (primeProfile (z : Complex)).re =
      tsum (fun p : Nat.Primes =>
        Real.log (1 + primeProfileWeight (p : Nat) * z) -
          Real.log (1 + primeProfileWeight (p : Nat)) * z) := by
  let g : Nat.Primes -> Real := fun p =>
    Real.log (1 + primeProfileWeight (p : Nat) * z) -
      Real.log (1 + primeProfileWeight (p : Nat)) * z
  have hSum : Tendsto (fun S : Finset Nat.Primes => S.sum g)
      atTop (nhds (tsum g)) := (summable_primeProfile_logFactor z hz).hasSum
  have hNat := hSum.comp tendsto_primeProfilePrefixSet
  have hBall : Membership.mem (Metric.closedBall (0 : Complex) z) (z : Complex) := by
    simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hz, le_refl]
  have hComplex := (tendstoUniformlyOn_primePrefixProfile z hz).tendsto_at hBall
  have hReal := (Complex.continuous_re.tendsto (primeProfile (z : Complex))).comp hComplex
  have hLog : Tendsto (fun N : Nat => Real.log (primePrefixProfile N (z : Complex)).re)
      atTop (nhds (Real.log (primeProfile (z : Complex)).re)) :=
    (Real.continuousAt_log (primeProfile_re_pos z hz).ne').tendsto.comp hReal
  have hFinite : (fun N : Nat => Real.log (primePrefixProfile N (z : Complex)).re) =
      (fun N : Nat => (primeProfilePrefixSet N).sum g) := by
    funext N
    rw [primePrefixProfile_ofReal_eq_exp N z hz, Complex.ofReal_re, Real.log_exp]
  rw [hFinite] at hLog
  exact tendsto_nhds_unique hLog hNat

theorem primeProfile_log_tail_eq_tsum (N : Nat) (z : Real) (hz : 0 <= z) :
    Real.log (primeProfile (z : Complex)).re -
        Real.log (primePrefixProfile N (z : Complex)).re =
      tsum (fun p : {p : Nat.Primes // N < (p : Nat)} =>
        Real.log (1 + primeProfileWeight (p.val : Nat) * z) -
          Real.log (1 + primeProfileWeight (p.val : Nat)) * z) := by
  classical
  have hSum := @Summable.sum_add_tsum_subtype_compl Real Nat.Primes
    _ _ _ _ _ (fun p : Nat.Primes =>
      Real.log (1 + primeProfileWeight (p : Nat) * z) -
        Real.log (1 + primeProfileWeight (p : Nat)) * z)
    (summable_primeProfile_logFactor z hz) (primeProfilePrefixSet N)
  have hPredicate :
      (fun p : Nat.Primes => Not (Membership.mem (primeProfilePrefixSet N) p)) =
      (fun p : Nat.Primes => N < (p : Nat)) := by
    funext p
    apply propext
    exact (not_congr (mem_primeProfilePrefixSet p N)).trans not_le
  rw [hPredicate] at hSum
  rw [log_primeProfile_eq_tsum z hz,
    primePrefixProfile_ofReal_eq_exp N z hz, Complex.ofReal_re, Real.log_exp]
  linarith only [hSum]

theorem primeProfile_log_tail_nonneg
    (N : Nat) (z : Real) (hz : 0 <= z) (hzOne : z <= 1) :
    0 <= Real.log (primeProfile (z : Complex)).re -
      Real.log (primePrefixProfile N (z : Complex)).re := by
  rw [primeProfile_log_tail_eq_tsum N z hz]
  apply tsum_nonneg
  intro p
  let a := primeProfileWeight (p.val : Nat)
  have ha : 0 <= a := primeProfileWeight_nonneg _
  have hBase : 0 < 1 + a := by positivity
  have hBernoulli := rpow_one_add_le_one_add_mul_self
    (by linarith : -1 <= a) hz hzOne
  have hLog := Real.log_le_log (Real.rpow_pos_of_pos hBase z) hBernoulli
  rw [Real.log_rpow hBase, mul_comm z a] at hLog
  change 0 <= Real.log (1 + a * z) - Real.log (1 + a) * z
  nlinarith only [hLog]

theorem primeProfile_log_tail_nonpos
    (N : Nat) (z : Real) (hzOne : 1 <= z) :
    Real.log (primeProfile (z : Complex)).re -
      Real.log (primePrefixProfile N (z : Complex)).re <= 0 := by
  have hz : 0 <= z := zero_le_one.trans hzOne
  rw [primeProfile_log_tail_eq_tsum N z hz]
  apply tsum_nonpos
  intro p
  let a := primeProfileWeight (p.val : Nat)
  have ha : 0 <= a := primeProfileWeight_nonneg _
  have hBase : 0 < 1 + a := by positivity
  have hInput : 0 < 1 + z * a := by positivity
  have hBernoulli := one_add_mul_self_le_rpow_one_add (by linarith : -1 <= a) hzOne
  have hLog := Real.log_le_log hInput hBernoulli
  rw [Real.log_rpow hBase, mul_comm z a] at hLog
  change Real.log (1 + a * z) - Real.log (1 + a) * z <= 0
  nlinarith only [hLog]

end PrimeFactorOscillations
