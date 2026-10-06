/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticProfileTail

/-! # The entire family profile is the exact positive logarithmic product -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open Filter

theorem complexFactor_ofReal_eq_exp (law : QuadraticPrimeLaw) (p : Nat.Primes)
    (t : Real) (ht : 0 <= t) :
    law.complexFactor p (t : Complex) = (Real.exp (law.logFactor t p) : Complex) := by
  have hpos : 0 < 1 + law.weight p * t := by
    have h := mul_nonneg (law.weight_nonneg p) ht
    linarith
  unfold complexFactor logFactor
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hpos]
  push_cast
  congr 1
  congr 1
  ring

theorem complexPrefix_ofReal_eq_exp (law : QuadraticPrimeLaw) (N : Nat)
    (t : Real) (ht : 0 <= t) :
    law.complexPrefix N (t : Complex) =
      (Real.exp ((primeProfilePrefixSet N).sum (law.logFactor t)) : Complex) := by
  rw [Real.exp_sum]
  simp only [Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun p _ => law.complexFactor_ofReal_eq_exp p t ht)

theorem complexProfile_ofReal_eq_exp (law : QuadraticPrimeLaw) (t : Real) (ht : 0 <= t) :
    law.complexProfile (t : Complex) = (Real.exp (law.logProfile t) : Complex) := by
  have hNat := (Real.continuous_exp.tendsto (law.logProfile t)).comp
    ((law.summable_logFactor t ht).hasSum.comp tendsto_primeProfilePrefixSet)
  have hCast := (Complex.continuous_ofReal.tendsto (Real.exp (law.logProfile t))).comp hNat
  have hReal : Tendsto (fun N : Nat => law.complexPrefix N (t : Complex)) atTop
      (nhds (Real.exp (law.logProfile t) : Complex)) := by
    apply hCast.congr'
    filter_upwards [] with N
    exact (law.complexPrefix_ofReal_eq_exp N t ht).symm
  have hBall : Membership.mem (Metric.closedBall (0 : Complex) t) (t : Complex) := by
    simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht, le_rfl]
  exact tendsto_nhds_unique ((law.tendstoUniformlyOn_complexPrefix t ht).tendsto_at hBall) hReal

theorem complexProfile_re_pos (law : QuadraticPrimeLaw) (t : Real) (ht : 0 <= t) :
    0 < (law.complexProfile (t : Complex)).re := by
  rw [law.complexProfile_ofReal_eq_exp t ht, Complex.ofReal_re]
  exact Real.exp_pos _

theorem logTailConstant_mono (law : QuadraticPrimeLaw) (a b : Real)
    (ha : 0 <= a) (hab : a <= b) : law.logTailConstant a <= law.logTailConstant b := by
  have hD := law.error_nonneg
  have hNu := law.nu_pos
  unfold logTailConstant
  gcongr

theorem positiveLowerBound_pos (law : QuadraticPrimeLaw) (b : Real) :
    0 < law.positiveLowerBound b := Real.exp_pos _

theorem complexProfile_re_lower_bound (law : QuadraticPrimeLaw) (b t : Real)
    (hb : 0 <= b) (ht : 0 <= t) (htb : t <= b) :
    law.positiveLowerBound b <= (law.complexProfile (t : Complex)).re := by
  have hSum := (summable_primeProfileWeight_sq.mul_left (law.logTailConstant t)).hasSum
  have hBound := tsum_of_norm_bounded hSum (fun p =>
    (show norm (law.logFactor t p) <= law.logTailConstant t *
      (primeProfileWeight (p : Nat)) ^ 2 from by
      simpa only [Real.norm_eq_abs] using law.abs_logFactor_le t ht p))
  have hMass : 0 <= tsum (fun p : Nat.Primes => (primeProfileWeight (p : Nat)) ^ 2) :=
    tsum_nonneg (fun p => sq_nonneg _)
  have hConst := mul_le_mul_of_nonneg_right (law.logTailConstant_mono t b ht htb) hMass
  rw [law.complexProfile_ofReal_eq_exp t ht, Complex.ofReal_re]
  apply Real.exp_le_exp.mpr
  change -(law.logTailConstant b * tsum (fun p : Nat.Primes =>
    (primeProfileWeight (p : Nat)) ^ 2)) <= law.logProfile t
  have hAbs : abs (law.logProfile t) <= law.logTailConstant t *
      tsum (fun p : Nat.Primes => (primeProfileWeight (p : Nat)) ^ 2) := by
    simpa only [Real.norm_eq_abs, logProfile, tsum_mul_left] using hBound
  linarith only [(abs_le.mp hAbs).1, hConst]

end PrimeFactorOscillations.QuadraticPrimeLaw
