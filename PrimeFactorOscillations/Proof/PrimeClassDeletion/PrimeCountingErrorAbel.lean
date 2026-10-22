/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import PrimeFactorOscillations.Helpers.GapFrequencyCoverage
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassAbel

/-!
# The complete signed prime-count error identity

The single-log reference Li_1 is distinct from the existing double-log
gap-count reference Li_2. Both lower endpoints and the full theta error
remain in the exact partial-summation consumer.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def primeLogarithmicIntegral (x : Real) : Real :=
  intervalIntegral (fun t : Real => 1 / Real.log t) 2 x volume

private theorem logInversePow_intervalIntegrable (k : Nat) (x : Real) (hx : 2 <= x) :
    IntervalIntegrable (fun t : Real => 1 / (Real.log t) ^ k) volume 2 x := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hx]
  apply continuousOn_const.div
  . exact (Real.continuousOn_log.mono (by
      intro t ht
      exact ne_of_gt (by linarith only [ht.1] : 0 < t))).pow k
  . intro t ht
    exact pow_ne_zero k (Real.log_pos (by linarith only [ht.1] : 1 < t)).ne'

theorem primeLogarithmicIntegral_eq_boundary_add_double_log_integral
    (x : Real) (hx : 2 <= x) :
    primeLogarithmicIntegral x =
      x / Real.log x - 2 / Real.log 2 + logarithmicIntegralTwo x := by
  have hI1 : IntervalIntegrable (fun t : Real => 1 / Real.log t) volume 2 x := by
    simpa only [pow_one] using logInversePow_intervalIntegrable 1 x hx
  have hI2 := logInversePow_intervalIntegrable 2 x hx
  have hDeriv : forall t : Real, Membership.mem (Set.uIcc (2 : Real) x) t ->
      HasDerivAt (fun y : Real => y / Real.log y)
        (1 / Real.log t - 1 / (Real.log t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith only [ht.1]
    have hL : 0 < Real.log t := Real.log_pos (by linarith only [ht.1])
    have h := (hasDerivAt_id t).div (Real.hasDerivAt_log ht0.ne') hL.ne'
    change HasDerivAt (fun y : Real => y / Real.log y)
      ((1 * Real.log t - t * Inv.inv t) / (Real.log t) ^ 2) t at h
    convert h using 1; field_simp [hL.ne', ht0.ne']
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv (hI1.sub hI2)
  rw [intervalIntegral.integral_sub hI1 hI2] at h
  change primeLogarithmicIntegral x - logarithmicIntegralTwo x =
    x / Real.log x - 2 / Real.log 2 at h
  linarith only [h]

theorem primeClassCount_error_abel (P : Set Nat) (x : Real) (hx : 2 <= x) :
    ((primeClassPrefix P (Nat.floor x)).card : Real) - primeLogarithmicIntegral x =
      2 / Real.log 2 + (primeClassThetaReal P x - x) / Real.log x +
        intervalIntegral (fun t =>
          (primeClassThetaReal P t - t) / (t * (Real.log t) ^ 2)) 2 x volume := by
  have hITheta := primeClassAbel_intervalIntegrable P x hx
  have hI2 := logInversePow_intervalIntegrable 2 x hx
  have hError : intervalIntegral (fun t =>
        (primeClassThetaReal P t - t) / (t * (Real.log t) ^ 2)) 2 x volume =
      intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
        2 x volume - logarithmicIntegralTwo x := by
    calc
      _ = intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2) 2 x volume := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        have ht0 : 0 < t := by linarith only [ht.1]
        field_simp [ht0.ne']
      _ = _ := by
        rw [intervalIntegral.integral_sub hITheta hI2]
        rfl
  rw [primeClassCount_abel P x hx,
    primeLogarithmicIntegral_eq_boundary_add_double_log_integral x hx, hError]
  ring

theorem primeCounting_error_abel (x : Real) (hx : 2 <= x) :
    (Nat.primeCounting (Nat.floor x) : Real) - primeLogarithmicIntegral x =
      2 / Real.log 2 + (Chebyshev.theta x - x) / Real.log x +
        intervalIntegral (fun t =>
          (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) 2 x volume := by
  simpa only [primeClassPrefix_univ_card_eq_primeCounting,
    primeClassThetaReal_univ_eq_chebyshev] using primeClassCount_error_abel Set.univ x hx

theorem primeClassCount_error_bound_of_theta_bound
    (P : Set Nat) (r C x : Real) (hr : 0 < r) (hC : 0 <= C)
    (hx : 2 <= x) (hLog : 1 <= Real.log x)
    (hTheta : forall t : Real, 2 <= t ->
      abs (primeClassThetaReal P t - t) <= C * t ^ r * (Real.log t) ^ 2) :
    abs (((primeClassPrefix P (Nat.floor x)).card : Real) - primeLogarithmicIntegral x) <=
      (2 / Real.log 2 + C + C / r) * x ^ r * Real.log x := by
  let f : Real -> Real := fun t =>
    (primeClassThetaReal P t - t) / (t * (Real.log t) ^ 2)
  let g : Real -> Real := fun t => C * t ^ (r - 1)
  have hx0 : 0 < x := by linarith only [hx]
  have hLx : 0 < Real.log x := by linarith only [hLog]
  have hL2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hFInt : IntervalIntegrable f volume 2 x := by
    apply IntervalIntegrable.congr _
      ((primeClassAbel_intervalIntegrable P x hx).sub (logInversePow_intervalIntegrable 2 x hx))
    intro t ht
    rw [Set.uIoc_of_le hx] at ht
    have ht0 : 0 < t := by linarith only [ht.1]
    dsimp only [f]
    field_simp [ht0.ne']
  have hGInt : IntervalIntegrable g volume 2 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith only [hr])).const_mul C
  have hPoint : forall t : Real, Membership.mem (Set.Icc (2 : Real) x) t ->
      abs (f t) <= g t := by
    intro t ht
    have ht0 : 0 < t := by linarith only [ht.1]
    have hL : 0 < Real.log t := Real.log_pos (by linarith only [ht.1])
    have hPow : t ^ r / t = t ^ (r - 1) := by
      rw [Real.rpow_sub ht0, Real.rpow_one]
    dsimp only [f, g]
    rw [abs_div, abs_of_pos (mul_pos ht0 (pow_pos hL 2))]
    calc
      abs (primeClassThetaReal P t - t) / (t * (Real.log t) ^ 2) <=
          (C * t ^ r * (Real.log t) ^ 2) / (t * (Real.log t) ^ 2) :=
        div_le_div_of_nonneg_right (hTheta t ht.1) (by positivity)
      _ = C * (t ^ r / t) := by field_simp [hL.ne', ht0.ne']
      _ = C * t ^ (r - 1) := by rw [hPow]
  have hUpper := intervalIntegral.integral_mono_on hx hFInt hGInt
    (fun t ht => (abs_le.mp (hPoint t ht)).2)
  have hLower := intervalIntegral.integral_mono_on hx hGInt.neg hFInt
    (fun t ht => (abs_le.mp (hPoint t ht)).1)
  change intervalIntegral (fun t : Real => -(g t)) 2 x volume <=
    intervalIntegral f 2 x volume at hLower
  rw [intervalIntegral.integral_neg] at hLower
  have hAbsIntegral : abs (intervalIntegral f 2 x volume) <= intervalIntegral g 2 x volume :=
    abs_le.mpr (And.intro (by linarith only [hLower]) hUpper)
  have hGValue : intervalIntegral g 2 x volume = C * ((x ^ r - (2 : Real) ^ r) / r) := by
    dsimp only [g]
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith only [hr])), show r - 1 + 1 = r by ring]
  have hGUpper : intervalIntegral g 2 x volume <= (C / r) * x ^ r := by
    rw [hGValue]
    calc
      C * ((x ^ r - (2 : Real) ^ r) / r) <= C * (x ^ r / r) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg (by norm_num) r)) hr.le) hC
      _ = (C / r) * x ^ r := by ring
  have hIntegral : abs (intervalIntegral f 2 x volume) <= (C / r) * x ^ r :=
    hAbsIntegral.trans hGUpper
  have hEndpoint : abs ((primeClassThetaReal P x - x) / Real.log x) <=
      C * x ^ r * Real.log x := by
    rw [abs_div, abs_of_pos hLx]
    calc
      abs (primeClassThetaReal P x - x) / Real.log x <=
          (C * x ^ r * (Real.log x) ^ 2) / Real.log x :=
        div_le_div_of_nonneg_right (hTheta x hx) hLx.le
      _ = C * x ^ r * Real.log x := by field_simp [hLx.ne']
  have hPower0 : 0 <= x ^ r := Real.rpow_nonneg hx0.le r
  have hPowerOne : 1 <= x ^ r := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (by linarith only [hx] : 1 <= x) hr.le
  have hPowerLogOne : 1 <= x ^ r * Real.log x := by
    simpa only [one_mul] using mul_le_mul hPowerOne hLog
      (by norm_num : (0 : Real) <= 1) hPower0
  have hConstant0 : 0 <= 2 / Real.log (2 : Real) := div_nonneg (by norm_num) hL2.le
  have hConstantPay := mul_le_mul_of_nonneg_left hPowerLogOne hConstant0
  have hIntegralPay := mul_le_mul_of_nonneg_left hLog
    (mul_nonneg (div_nonneg hC hr.le) hPower0)
  rw [mul_one] at hConstantPay hIntegralPay
  have hExact := primeClassCount_error_abel P x hx
  change ((primeClassPrefix P (Nat.floor x)).card : Real) - primeLogarithmicIntegral x =
    2 / Real.log 2 + (primeClassThetaReal P x - x) / Real.log x +
      intervalIntegral f 2 x volume at hExact
  rw [hExact]
  have hTriangle : abs (2 / Real.log 2 + (primeClassThetaReal P x - x) / Real.log x +
        intervalIntegral f 2 x volume) <=
      2 / Real.log 2 + abs ((primeClassThetaReal P x - x) / Real.log x) +
        abs (intervalIntegral f 2 x volume) := by
    have h1 : abs (2 / Real.log 2 + (primeClassThetaReal P x - x) / Real.log x +
        intervalIntegral f 2 x volume) <=
        abs (2 / Real.log 2 + (primeClassThetaReal P x - x) / Real.log x) +
          abs (intervalIntegral f 2 x volume) := by
      simpa only [Real.norm_eq_abs] using
        norm_add_le (2 / Real.log 2 + (primeClassThetaReal P x - x) / Real.log x)
          (intervalIntegral f 2 x volume)
    have h2 : abs (2 / Real.log 2 + (primeClassThetaReal P x - x) / Real.log x) <=
        abs (2 / Real.log (2 : Real)) + abs ((primeClassThetaReal P x - x) / Real.log x) := by
      simpa only [Real.norm_eq_abs] using
        norm_add_le (2 / Real.log (2 : Real)) ((primeClassThetaReal P x - x) / Real.log x)
    rw [abs_of_nonneg hConstant0] at h2
    linarith only [h1, h2]
  calc
    _ <= 2 / Real.log 2 + C * x ^ r * Real.log x + (C / r) * x ^ r := by
      linarith only [hTriangle, hEndpoint, hIntegral]
    _ <= (2 / Real.log 2) * (x ^ r * Real.log x) +
        C * x ^ r * Real.log x + (C / r) * x ^ r * Real.log x := by
      nlinarith only [hConstantPay, hIntegralPay]
    _ = (2 / Real.log 2 + C + C / r) * x ^ r * Real.log x := by ring

theorem primeCounting_error_bound_of_theta_bound
    (r C x : Real) (hr : 0 < r) (hC : 0 <= C)
    (hx : 2 <= x) (hLog : 1 <= Real.log x)
    (hTheta : forall t : Real, 2 <= t ->
      abs (Chebyshev.theta t - t) <= C * t ^ r * (Real.log t) ^ 2) :
    abs ((Nat.primeCounting (Nat.floor x) : Real) - primeLogarithmicIntegral x) <=
      (2 / Real.log 2 + C + C / r) * x ^ r * Real.log x := by
  simpa only [primeClassPrefix_univ_card_eq_primeCounting] using
    primeClassCount_error_bound_of_theta_bound Set.univ r C x hr hC hx hLog
      (by
        intro t ht
        simpa only [primeClassThetaReal_univ_eq_chebyshev] using hTheta t ht)

end PrimeFactorOscillations.PrimeClassDeletion
