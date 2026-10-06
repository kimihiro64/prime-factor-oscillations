/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.MomentEnvelopeLimit

/-!
# The complete fixed-second-moment area consumer

A hypothetical second-moment bound for the actual signed psi-tail integral
implies an area upper bound of size sqrt(x)/log(x), with an explicit
conservative factor eight. Together with the envelope comparison, this
quantifies the loss of that particular route without claiming a lower
bound for actual area or a failure of the positive-area approach itself.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter MeasureTheory Set Robin1984

theorem nicolas_wave_second_moment_upper
    (x : Real) (hx : 2 <= x) :
    lintegral (volume.restrict (Icc x (2 * x)))
        (fun y : Real => ENNReal.ofReal (abs (nicolasMomentWave y) ^ (2 : Nat))) <=
      ENNReal.ofReal (8 * x * (Real.log x) ^ (2 : Nat)) *
        lintegral (volume.restrict (Icc x (2 * x)))
          (fun y : Real => ENNReal.ofReal ((nicolasJ y) ^ (2 : Nat))) := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hPoint : Filter.Eventually (fun y : Real =>
      ENNReal.ofReal (abs (nicolasMomentWave y) ^ (2 : Nat)) <=
        ENNReal.ofReal (8 * x * (Real.log x) ^ (2 : Nat)) *
          ENNReal.ofReal ((nicolasJ y) ^ (2 : Nat)))
      (ae (volume.restrict (Icc x (2 * x)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hy0 : 0 < y := hx0.trans_le hy.1
    have hly : 0 < Real.log y := Real.log_pos (hx1.trans_le hy.1)
    have hLog := Real.log_le_log hy0 hy.2
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hx0.ne'] at hLog
    have hLogTwo : Real.log 2 <= Real.log x := Real.log_le_log (by norm_num) hx
    have hLogSq : (Real.log y) ^ (2 : Nat) <= 4 * (Real.log x) ^ (2 : Nat) := by
      nlinarith
    have hCoeff := mul_le_mul hy.2 hLogSq (sq_nonneg (Real.log y)) (by positivity : 0 <= 2 * x)
    have hSq : (y ^ (1 / 2 : Real)) ^ (2 : Nat) = y := by
      rw [pow_two, <- Real.rpow_add hy0]
      norm_num
    have hIdentity : abs (nicolasMomentWave y) ^ (2 : Nat) =
        (y * (Real.log y) ^ (2 : Nat)) * (nicolasJ y) ^ (2 : Nat) := by
      rw [sq_abs, nicolasMomentWave, mul_pow, mul_pow, hSq]
    have hBound := mul_le_mul_of_nonneg_right hCoeff (sq_nonneg (nicolasJ y))
    rw [hIdentity]
    calc
      _ <= ENNReal.ofReal ((8 * x * (Real.log x) ^ (2 : Nat)) * (nicolasJ y) ^ (2 : Nat)) :=
        ENNReal.ofReal_le_ofReal (by nlinarith only [hBound])
      _ = _ := ENNReal.ofReal_mul (by positivity)
  have h := lintegral_mono_ae hPoint
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  exact h


theorem eventually_nicolasPositiveArea_of_second_moment
    (C : Real) (_hC : 0 <= C)
    (hMoment : Filter.Eventually (fun x : Real =>
      lintegral (volume.restrict (Icc x (2 * x)))
        (fun y : Real => ENNReal.ofReal ((nicolasJ y) ^ (2 : Nat))) <=
          ENNReal.ofReal (C / (Real.log x) ^ (2 : Nat))) atTop) :
    Filter.Eventually (fun x : Real =>
      nicolasPositiveArea x <= ENNReal.ofReal
        (8 * C * x ^ (1 / 2 : Real) / Real.log x)) atTop := by
  choose Y hY using eventually_atTop.mp eventually_nicolasLog_le_moment_wave
  filter_upwards [hMoment, eventually_ge_atTop Y, eventually_ge_atTop (3 : Real)]
    with x hm hxY hxThree
  have hx : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hp : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hx0 _
  have hArea := nicolasPositiveArea_le_moment 2 (by norm_num) x hx
    (fun y hxy _ => hY y (hxY.trans hxy))
  have hSecond := nicolas_wave_second_moment_upper x (by linarith)
  have hPow : (x ^ (1 / 2 : Real)) ^ (2 : Nat) = x := by
    rw [pow_two, <- Real.rpow_add hx0]
    norm_num
  have hIdentity :
      (1 / (x ^ (1 / 2 : Real) * Real.log x)) *
        ((8 * x * (Real.log x) ^ (2 : Nat)) * (C / (Real.log x) ^ (2 : Nat))) =
        8 * C * x ^ (1 / 2 : Real) / Real.log x := by
    field_simp
    nlinarith only [congrArg (fun t : Real => 8 * C * t) hPow]
  calc
    _ <= ENNReal.ofReal (1 / (x ^ (1 / 2 : Real) * Real.log x)) *
        (ENNReal.ofReal (8 * x * (Real.log x) ^ (2 : Nat)) *
          ENNReal.ofReal (C / (Real.log x) ^ (2 : Nat))) :=
      hArea.trans (mul_le_mul_of_nonneg_left
        (hSecond.trans (mul_le_mul_of_nonneg_left hm (by positivity))) (by positivity))
    _ = ENNReal.ofReal ((1 / (x ^ (1 / 2 : Real) * Real.log x)) *
        ((8 * x * (Real.log x) ^ (2 : Nat)) * (C / (Real.log x) ^ (2 : Nat)))) := by
      rw [<- ENNReal.ofReal_mul (by positivity : 0 <= 8 * x * (Real.log x) ^ (2 : Nat))]
      exact (ENNReal.ofReal_mul
        (by positivity : 0 <= 1 / (x ^ (1 / 2 : Real) * Real.log x))).symm
    _ = _ := by rw [hIdentity]


end PrimeFactorOscillations
