/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfile

/-!
# Positivity of the real prime profile

Exact exponential finite products give a common strictly positive lower bound
on every compact nonnegative real interval, inherited by the entire limit.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem primePrefixProfile_ofReal_eq_exp (N : Nat) (t : Real) (ht : 0 <= t) :
    primePrefixProfile N (t : Complex) =
      (Real.exp ((primeProfilePrefixSet N).sum (fun p =>
        Real.log (1 + primeProfileWeight (p : Nat) * t) -
          Real.log (1 + primeProfileWeight (p : Nat)) * t)) : Complex) := by
  rw [Real.exp_sum]
  simp only [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro p hp
  exact Complex.normalizedLinearFactor_ofReal_eq (primeProfileWeight (p : Nat)) t
    (primeProfileWeight_nonneg (p : Nat)) ht

theorem primePrefixProfile_im_eq_zero (N : Nat) (t : Real) (ht : 0 <= t) :
    (primePrefixProfile N (t : Complex)).im = 0 := by
  rw [primePrefixProfile_ofReal_eq_exp N t ht]
  exact Complex.ofReal_im _

theorem primePrefixProfile_re_lower_bound (N : Nat) (b t : Real)
    (hb : 0 <= b) (ht : 0 <= t) (htb : t <= b) :
    Real.exp (-(b ^ 2 * tsum (fun p : Nat.Primes =>
      (primeProfileWeight (p : Nat)) ^ 2)) / 2) <=
        (primePrefixProfile N (t : Complex)).re := by
  rw [primePrefixProfile_ofReal_eq_exp N t ht, Complex.ofReal_re]
  apply Real.exp_le_exp.mpr
  have hsum : (primeProfilePrefixSet N).sum
      (fun p => (primeProfileWeight (p : Nat)) ^ 2) <=
        tsum (fun p : Nat.Primes => (primeProfileWeight (p : Nat)) ^ 2) := by
    exact Summable.sum_le_tsum (primeProfilePrefixSet N)
      (fun p hp => sq_nonneg (primeProfileWeight (p : Nat)))
      summable_primeProfileWeight_sq
  calc
    -(b ^ 2 * tsum (fun p : Nat.Primes =>
        (primeProfileWeight (p : Nat)) ^ 2)) / 2 <=
        -(b ^ 2 * (primeProfilePrefixSet N).sum
          (fun p => (primeProfileWeight (p : Nat)) ^ 2)) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg b)]
    _ = (primeProfilePrefixSet N).sum
        (fun p => -(b ^ 2 * (primeProfileWeight (p : Nat)) ^ 2) / 2) := by
      rw [Finset.mul_sum, <- Finset.sum_neg_distrib, Finset.sum_div]
    _ <= (primeProfilePrefixSet N).sum (fun p =>
        Real.log (1 + primeProfileWeight (p : Nat) * t) -
          Real.log (1 + primeProfileWeight (p : Nat)) * t) := by
      apply Finset.sum_le_sum
      intro p hp
      let a := primeProfileWeight (p : Nat)
      have ha : 0 <= a := primeProfileWeight_nonneg (p : Nat)
      have hlog := Real.sub_log_one_add_bounds a ha
      have hlogt := Real.sub_log_one_add_bounds (a * t) (mul_nonneg ha ht)
      have hsq : t ^ 2 <= b ^ 2 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg a)
      have hlmul := mul_le_mul_of_nonneg_right hlog.1 ht
      dsimp [a] at hlog hlogt hmul hlmul
      nlinarith

theorem primeProfile_im_eq_zero (t : Real) (ht : 0 <= t) :
    (primeProfile (t : Complex)).im = 0 := by
  have hz : Membership.mem (Metric.closedBall (0 : Complex) t) (t : Complex) := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht]
  have hlim := (tendstoUniformlyOn_primePrefixProfile t ht).tendsto_at hz
  have him := Complex.continuous_im.tendsto (primeProfile (t : Complex))
  have hc := him.comp hlim
  have hzlim : Filter.Tendsto (fun N : Nat =>
      (primePrefixProfile N (t : Complex)).im) Filter.atTop (nhds 0) := by
    simpa only [primePrefixProfile_im_eq_zero _ t ht] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : Nat => (0 : Real))
        Filter.atTop (nhds 0))
  exact tendsto_nhds_unique hc hzlim

theorem primeProfile_re_lower_bound (b t : Real)
    (hb : 0 <= b) (ht : 0 <= t) (htb : t <= b) :
    Real.exp (-(b ^ 2 * tsum (fun p : Nat.Primes =>
      (primeProfileWeight (p : Nat)) ^ 2)) / 2) <=
        (primeProfile (t : Complex)).re := by
  have hz : Membership.mem (Metric.closedBall (0 : Complex) b) (t : Complex) := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht] using htb
  have hlim := (tendstoUniformlyOn_primePrefixProfile b hb).tendsto_at hz
  have hre := Complex.continuous_re.tendsto (primeProfile (t : Complex))
  apply ge_of_tendsto' (hre.comp hlim)
  intro N
  exact primePrefixProfile_re_lower_bound N b t hb ht htb

theorem primeProfile_re_pos (t : Real) (ht : 0 <= t) :
    0 < (primeProfile (t : Complex)).re := by
  exact (Real.exp_pos _).trans_le (primeProfile_re_lower_bound t t ht ht le_rfl)

end PrimeFactorOscillations

