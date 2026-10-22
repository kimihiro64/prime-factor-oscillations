/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import PrimeFactorOscillations.Helpers.GapFrequencyCoverage
import PrimeFactorOscillations.Helpers.NicolasStripDegreeLocalization
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

theorem primeClassThetaReal_initial_error_bound
    (P : Set Nat) (Y t : Real) (hY : 2 <= Y) (ht : 2 <= t) (htY : t <= Y) :
    abs (primeClassThetaReal P t - t) <= (Y + 1) * Real.log Y + Y := by
  classical
  have ht0 : 0 < t := by linarith only [ht]
  have hLY : 0 <= Real.log Y := Real.log_nonneg (by linarith only [hY])
  have hLt : 0 <= Real.log t := Real.log_nonneg (by linarith only [ht])
  have hCountNat : (primeClassPrefix P (Nat.floor t)).card <= Nat.floor t + 1 := by
    unfold primeClassPrefix
    calc
      _ <= (Finset.Icc 2 (Nat.floor t)).card := Finset.card_filter_le _ _
      _ <= Nat.floor t + 1 := by rw [Nat.card_Icc]; omega
  have hCount : ((primeClassPrefix P (Nat.floor t)).card : Real) <= Y + 1 := by
    have hCast : ((primeClassPrefix P (Nat.floor t)).card : Real) <=
        (Nat.floor t : Real) + 1 := by exact_mod_cast hCountNat
    have hFloor := Nat.floor_le ht0.le
    linarith only [hCast, hFloor, htY]
  have hLog := Real.log_le_log ht0 htY
  have hTheta := primeClassThetaReal_le_count_mul_log P t ht
  have hBound : primeClassThetaReal P t <= (Y + 1) * Real.log Y := by
    calc
      _ <= ((primeClassPrefix P (Nat.floor t)).card : Real) * Real.log t := hTheta
      _ <= (Y + 1) * Real.log t := mul_le_mul_of_nonneg_right hCount hLt
      _ <= (Y + 1) * Real.log Y :=
        mul_le_mul_of_nonneg_left hLog (by linarith only [hY])
  have hTheta0 := primeClassThetaReal_nonneg P t
  have hProduct0 : 0 <= (Y + 1) * Real.log Y :=
    mul_nonneg (by linarith only [hY]) hLY
  exact abs_le.mpr (And.intro
    (by linarith only [hTheta0, htY, hProduct0])
    (by linarith only [hBound, ht, hY]))

theorem primeClassThetaReal_global_error_of_tail_bound
    (P : Set Nat) (r C Y : Real) (hr : 0 < r) (hC : 0 <= C) (hY : 2 <= Y)
    (hTail : forall t : Real, Y <= t ->
      abs (primeClassThetaReal P t - t) <= C * t ^ r * (Real.log t) ^ 2)
    (t : Real) (ht : 2 <= t) :
    abs (primeClassThetaReal P t - t) <=
      (C + ((Y + 1) * Real.log Y + Y) / (Real.log 2) ^ 2) *
        t ^ r * (Real.log t) ^ 2 := by
  let B : Real := (Y + 1) * Real.log Y + Y
  have ht0 : 0 < t := by linarith only [ht]
  have hL2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hLY : 0 <= Real.log Y := Real.log_nonneg (by linarith only [hY])
  have hB : 0 <= B := by dsimp only [B]; positivity
  have hRatio : 0 <= B / (Real.log 2) ^ 2 := div_nonneg hB (sq_nonneg _)
  have hWeight : 0 <= t ^ r * (Real.log t) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg ht0.le r) (sq_nonneg _)
  change abs (primeClassThetaReal P t - t) <=
    (C + B / (Real.log 2) ^ 2) * t ^ r * (Real.log t) ^ 2
  by_cases hYt : Y <= t
  case pos =>
    have h := hTail t hYt
    nlinarith only [h, mul_nonneg hRatio hWeight]
  case neg =>
    have htY : t <= Y := le_of_lt (lt_of_not_ge hYt)
    have hInitial := primeClassThetaReal_initial_error_bound P Y t hY ht htY
    change abs (primeClassThetaReal P t - t) <= B at hInitial
    have hPower : 1 <= t ^ r := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le (by linarith only [ht] : 1 <= t) hr.le
    have hLog := Real.log_le_log (by norm_num : (0 : Real) < 2) ht
    have hSquare : (Real.log (2 : Real)) ^ 2 <= (Real.log t) ^ 2 := by
      nlinarith only [hLog, hL2]
    have hWeightLower : (Real.log (2 : Real)) ^ 2 <= t ^ r * (Real.log t) ^ 2 := by
      nlinarith only [hPower, hSquare, sq_nonneg (Real.log t)]
    have hPay := mul_le_mul_of_nonneg_left hWeightLower hRatio
    have hIdentity : B / (Real.log 2) ^ 2 * (Real.log 2) ^ 2 = B := by
      field_simp [hL2.ne']
    rw [hIdentity] at hPay
    nlinarith only [hInitial, hPay, mul_nonneg hC hWeight]

theorem primeClassCount_error_bound_of_eventual_theta_bound
    (P : Set Nat) (r C : Real) (hr : 0 < r) (hC : 0 <= C)
    (hTail : Filter.Eventually (fun t : Real =>
      abs (primeClassThetaReal P t - t) <= C * t ^ r * (Real.log t) ^ 2) Filter.atTop) :
    exists A : Real, And (0 <= A) (forall x : Real, 2 <= x -> 1 <= Real.log x ->
      abs (((primeClassPrefix P (Nat.floor x)).card : Real) - primeLogarithmicIntegral x) <=
        A * x ^ r * Real.log x) := by
  choose Y0 hAfter using Filter.eventually_atTop.mp hTail
  let Y : Real := max 2 Y0
  let D : Real := C + ((Y + 1) * Real.log Y + Y) / (Real.log 2) ^ 2
  have hY : 2 <= Y := le_max_left _ _
  have hLY : 0 <= Real.log Y := Real.log_nonneg (by linarith only [hY])
  have hD : 0 <= D := by dsimp only [D]; positivity
  have hGlobal : forall t : Real, 2 <= t ->
      abs (primeClassThetaReal P t - t) <= D * t ^ r * (Real.log t) ^ 2 := by
    intro t ht
    exact primeClassThetaReal_global_error_of_tail_bound P r C Y hr hC hY
      (fun u hu => hAfter u ((le_max_right 2 Y0).trans hu)) t ht
  refine Exists.intro (2 / Real.log 2 + D + D / r) (And.intro ?_ ?_)
  . have hL2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    positivity
  . intro x hx hL
    exact primeClassCount_error_bound_of_theta_bound P r D x hr hD hx hL hGlobal

theorem exists_thetaError_bound_of_uniform_zero_strip
    (eta delta : Real) (hEtaHalf : (1 / 2 : Real) <= eta) (hEtaOne : eta < 1)
    (hd : 0 < delta) (hdOne : delta <= 1)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= eta) :
    exists A : Real, And (0 < A) (forall x : Real, 2 <= x ->
      abs (Chebyshev.theta x - x) <=
        A * x ^ (eta + delta / 2) * (Real.log x) ^ 2) := by
  choose C hC hPsi using
    exists_nicolasPsiError_le_strip_rpow eta delta hEtaHalf hEtaOne hd hdOne hUpper
  let Y : Real := max 4 (2 * Real.exp 1)
  have hY : 2 <= Y := (by norm_num : (2 : Real) <= 4).trans (le_max_left _ _)
  have hExponent : 0 < eta + delta / 2 := by linarith only [hEtaHalf, hd]
  have hTail : forall x : Real, Y <= x ->
      abs (primeClassThetaReal Set.univ x - x) <=
        (C + 2) * x ^ (eta + delta / 2) * (Real.log x) ^ 2 := by
    intro x hxY
    have hx : 4 <= x := (le_max_left _ _).trans hxY
    have hx0 : 0 < x := by linarith only [hx]
    have hExp : 2 * Real.exp 1 <= x := (le_max_right _ _).trans hxY
    have hL : 1 <= Real.log (x / 2) := by
      have h := Real.log_le_log (Real.exp_pos 1)
        (show Real.exp 1 <= x / 2 by linarith only [hExp])
      simpa only [Real.log_exp] using h
    have hLx : 1 <= Real.log x :=
      hL.trans (Real.log_le_log (by positivity) (by linarith only [hx] : x / 2 <= x))
    have hLogSquare : 1 <= (Real.log x) ^ 2 := by nlinarith only [hLx]
    have hLogPay : Real.log x <= (Real.log x) ^ 2 := by nlinarith only [hLx]
    have hPower : Real.sqrt x <= x ^ (eta + delta / 2) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hx])
        (by linarith only [hEtaHalf, hd])
    have hPsiPay : abs (Chebyshev.psi x - x) <=
        C * x ^ (eta + delta / 2) * (Real.log x) ^ 2 := by
      exact (hPsi x hx hL).trans (by
        have h := mul_le_mul_of_nonneg_left hLogSquare
          (mul_nonneg hC.le (Real.rpow_nonneg hx0.le (eta + delta / 2)))
        simpa only [mul_one] using h)
    have hGapPay : 2 * Real.sqrt x * Real.log x <=
        2 * x ^ (eta + delta / 2) * (Real.log x) ^ 2 := by
      calc
        _ <= 2 * x ^ (eta + delta / 2) * Real.log x :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hPower (by norm_num)) (by linarith only [hLx])
        _ <= _ := mul_le_mul_of_nonneg_left hLogPay (by positivity)
    have hGap := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log
      (by linarith only [hx] : 1 <= x)
    have hTriangle := abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
    rw [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at hTriangle
    rw [primeClassThetaReal_univ_eq_chebyshev]
    nlinarith only [hPsiPay, hGapPay, hGap, hTriangle]
  let A : Real := C + 2 + ((Y + 1) * Real.log Y + Y) / (Real.log 2) ^ 2
  have hLY : 0 <= Real.log Y := Real.log_nonneg (by linarith only [hY])
  have hA : 0 < A := by dsimp only [A]; positivity
  refine Exists.intro A (And.intro hA ?_)
  intro x hx
  simpa only [primeClassThetaReal_univ_eq_chebyshev] using
    primeClassThetaReal_global_error_of_tail_bound Set.univ (eta + delta / 2)
      (C + 2) Y hExponent (by linarith only [hC]) hY hTail x hx

theorem primeCounting_error_bound_of_uniform_zero_strip
    (eta b : Real) (hEtaHalf : (1 / 2 : Real) <= eta) (hEtaOne : eta < 1)
    (hb : eta < b)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= eta) :
    exists A : Real, And (0 < A) (forall x : Real, 2 <= x -> 1 <= Real.log x ->
      abs ((Nat.primeCounting (Nat.floor x) : Real) - primeLogarithmicIntegral x) <=
        A * x ^ b * Real.log x) := by
  let delta : Real := min 1 (b - eta)
  have hd : 0 < delta := lt_min (by norm_num) (by linarith only [hb])
  have hdOne : delta <= 1 := min_le_left _ _
  have hExponent : 0 < eta + delta / 2 := by linarith only [hEtaHalf, hd]
  have hPowerOrder : eta + delta / 2 <= b := by
    have h := min_le_right (1 : Real) (b - eta)
    change delta <= b - eta at h
    linarith only [h, hd]
  choose C hC hTheta using
    exists_thetaError_bound_of_uniform_zero_strip
      eta delta hEtaHalf hEtaOne hd hdOne hUpper
  let A : Real := 2 / Real.log 2 + C + C / (eta + delta / 2)
  have hL2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine Exists.intro A (And.intro hA ?_)
  intro x hx hL
  have hCount := primeCounting_error_bound_of_theta_bound (eta + delta / 2) C x
    hExponent hC.le hx hL hTheta
  have hPower := Real.rpow_le_rpow_of_exponent_le
    (by linarith only [hx] : 1 <= x) hPowerOrder
  change abs ((Nat.primeCounting (Nat.floor x) : Real) - primeLogarithmicIntegral x) <=
    A * x ^ (eta + delta / 2) * Real.log x at hCount
  exact hCount.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hPower hA.le) (by linarith only [hL]))

end PrimeFactorOscillations.PrimeClassDeletion
