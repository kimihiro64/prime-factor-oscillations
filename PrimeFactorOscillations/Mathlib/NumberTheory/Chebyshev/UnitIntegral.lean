/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import PrimeFactorOscillations.Mathlib.NumberTheory.Chebyshev.UnitInterval

/-!
# Signed theta integrals on short intervals

Actual interval comparisons bound the theta error at adjacent maxima and
control the loss when a real endpoint is replaced by an integer.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set

namespace Real

theorem continuousOn_sub_mul_logTailKernel (A a b : Real) (ha : 1 < a) :
    ContinuousOn (fun t : Real =>
      (A - t) * ((1 / log t + 1 / (log t) ^ 2) / t ^ 2)) (Icc a b) := by
  intro t ht
  have htOne : 1 < t := ha.trans_le ht.1
  have htPos : 0 < t := lt_trans zero_lt_one htOne
  have htNe : Not (t = 0) := htPos.ne'
  have hLogNe : Not (log t = 0) := (log_pos htOne).ne'
  have htSquareNe : Not (t ^ 2 = 0) := pow_ne_zero 2 htNe
  have hLogSquareNe : Not ((log t) ^ 2 = 0) := pow_ne_zero 2 hLogNe
  have hAt : ContinuousAt (fun t : Real =>
      (A - t) * ((1 / log t + 1 / (log t) ^ 2) / t ^ 2)) t := by
    fun_prop
  exact hAt.continuousWithinAt

end Real

namespace Chebyshev

/-- The theta integrand on a unit interval has an exact continuous model. -/
theorem theta_error_unit_integral_eq (n : Nat) :
    intervalIntegral (fun t : Real => (theta t - t) *
        ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
        (n : Real) ((n : Real) + 1) volume =
      intervalIntegral (fun t : Real => (theta (n : Real) - t) *
        ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
        (n : Real) ((n : Real) + 1) volume := by
  apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
  intro t ht
  dsimp only
  rw [theta_eq_nat_of_mem_Ico n t ht.1.le ht.2]

/-- A positive right unit integral forces a positive theta error at its left endpoint. -/
theorem theta_error_pos_of_unit_integral_pos (n : Nat) (hn : 1 < (n : Real))
    (hPos : 0 < intervalIntegral (fun t : Real => (theta t - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
      (n : Real) ((n : Real) + 1) volume) :
    0 < theta (n : Real) - (n : Real) := by
  by_contra hNot
  have hError : theta (n : Real) - (n : Real) <= 0 := le_of_not_gt hNot
  rw [theta_error_unit_integral_eq] at hPos
  have hInt : IntervalIntegrable (fun t : Real => (theta (n : Real) - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
      volume (n : Real) ((n : Real) + 1) :=
    (Real.continuousOn_sub_mul_logTailKernel
    (theta (n : Real)) (n : Real) ((n : Real) + 1) hn).intervalIntegrable_of_Icc
      (by linarith : (n : Real) <= (n : Real) + 1)
  have hCompare := intervalIntegral.integral_mono_on
    (by linarith : (n : Real) <= (n : Real) + 1) hInt
    (intervalIntegrable_const : IntervalIntegrable (fun _ : Real => (0 : Real))
      volume (n : Real) ((n : Real) + 1)) (fun t ht => by
        have htOne : 1 < t := hn.trans_le ht.1
        have htPos : 0 < t := lt_trans zero_lt_one htOne
        have hL : 0 < Real.log t := Real.log_pos htOne
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.1]) (by positivity))
  have hNonpos : intervalIntegral (fun t : Real => (theta (n : Real) - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
      (n : Real) ((n : Real) + 1) volume <= 0 := by
    simpa using hCompare
  exact (not_lt_of_ge hNonpos) hPos

/-- The left maximum inequality bounds the next theta error by a logarithm. -/
theorem theta_error_succ_le_of_unit_integral_le
    (n : Nat) (hn : 1 < (n : Real)) (K : Real) (hK : 0 <= K)
    (hUpper : intervalIntegral (fun t : Real => (theta t - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
      (n : Real) ((n : Real) + 1) volume <= K / (((n : Real) + 1) * (n : Real))) :
    theta ((n + 1 : Nat) : Real) - ((n + 1 : Nat) : Real) <=
      (2 * K + 1) * Real.log ((n + 1 : Nat) : Real) := by
  let b : Real := (n : Real) + 1
  have hnPos : 0 < (n : Real) := lt_trans zero_lt_one hn
  have hbOne : 1 < b := by dsimp [b]; linarith
  have hbPos : 0 < b := lt_trans zero_lt_one hbOne
  have hL : 0 < Real.log b := Real.log_pos hbOne
  have hJump := theta_nat_succ_sub_le_log n
  simp only [Nat.cast_add, Nat.cast_one] at hJump
  change theta b - theta (n : Real) <= Real.log b at hJump
  simp only [Nat.cast_add, Nat.cast_one]
  change theta b - b <= (2 * K + 1) * Real.log b
  by_cases hSmall : theta (n : Real) - (n : Real) <= 1
  . have hError : theta b - b <= Real.log b := by dsimp [b] at *; linarith
    have hCredit := mul_nonneg hK hL.le
    nlinarith
  . let a : Real := theta (n : Real) - (n : Real) - 1
    have ha : 0 < a := by dsimp [a]; linarith
    have hInt : IntervalIntegrable (fun t : Real => (theta (n : Real) - t) *
        ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
        volume (n : Real) b :=
      (Real.continuousOn_sub_mul_logTailKernel
      (theta (n : Real)) (n : Real) b hn).intervalIntegrable_of_Icc
        (by dsimp [b]; linarith : (n : Real) <= b)
    have hCompare := intervalIntegral.integral_mono_on
      (by dsimp [b]; linarith : (n : Real) <= b)
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : Real => a / (b ^ 2 * Real.log b)) volume (n : Real) b)
      hInt (fun t ht => by
        have htOne : 1 < t := hn.trans_le ht.1
        have hKernel := Real.one_div_sq_mul_log_le_tailKernel t b htOne ht.2
        have hA : a <= theta (n : Real) - t := by
          dsimp [a, b] at *
          linarith [ht.2]
        calc
          a / (b ^ 2 * Real.log b) = a * (1 / (b ^ 2 * Real.log b)) := by ring
          _ <= (theta (n : Real) - t) *
              ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2) :=
            mul_le_mul hA hKernel (by positivity) (ha.le.trans hA))
    have hIntegralLower : a / (b ^ 2 * Real.log b) <=
        intervalIntegral (fun t : Real => (theta (n : Real) - t) *
          ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
          (n : Real) b volume := by
      simpa [b] using hCompare
    rw [theta_error_unit_integral_eq] at hUpper
    have hBound : a / (b ^ 2 * Real.log b) <= K / (b * (n : Real)) :=
      hIntegralLower.trans hUpper
    have hIdentity : K / (b * (n : Real)) =
        (K * b * Real.log b / (n : Real)) / (b ^ 2 * Real.log b) := by
      field_simp [hnPos.ne', hbPos.ne', hL.ne']
    rw [hIdentity] at hBound
    have hAUpper : a <= K * b * Real.log b / (n : Real) :=
      (div_le_div_iff_of_pos_right (by positivity : 0 < b ^ 2 * Real.log b)).mp hBound
    have hbLe : b <= 2 * (n : Real) := by dsimp [b]; linarith
    have hProduct := mul_le_mul_of_nonneg_left hbLe (mul_nonneg hK hL.le)
    have hQuotient : K * b * Real.log b / (n : Real) <= 2 * K * Real.log b := by
      calc
        K * b * Real.log b / (n : Real) <=
            (2 * K * Real.log b * (n : Real)) / (n : Real) :=
          (div_le_div_iff_of_pos_right hnPos).2 (by nlinarith)
        _ = 2 * K * Real.log b := by field_simp [hnPos.ne']
    have hAFinal := hAUpper.trans hQuotient
    dsimp [a, b] at *
    linarith

/-- Elementary control of the actual theta-tail over every interval of length at most one. -/
theorem theta_error_short_integral_abs_le
    (a b : Real) (ha : 0 < a) (hLog : 1 <= Real.log a)
    (hab : a <= b) (hLength : b <= a + 1) :
    abs (intervalIntegral (fun t : Real => (theta t - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) a b volume) <= 2 / a := by
  have hBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := 2 / a)
    (f := fun t : Real => (theta t - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) (fun t ht => by
        rw [uIoc_of_le hab] at ht
        have htPos : 0 < t := ha.trans ht.1
        have hLogT : 1 <= Real.log t := hLog.trans (Real.log_le_log ha ht.1.le)
        have hAbs := theta_error_tailKernel_abs_le t htPos hLogT
        have hDiv : 2 / t <= 2 / a :=
          div_le_div_of_nonneg_left (by norm_num) ha ht.1.le
        simpa only [Real.norm_eq_abs] using hAbs.trans hDiv)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hBound
  have hError : 0 <= (2 / a) * (1 - (b - a)) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith

end Chebyshev
