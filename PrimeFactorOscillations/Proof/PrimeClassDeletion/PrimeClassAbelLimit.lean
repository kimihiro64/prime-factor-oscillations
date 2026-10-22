/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassAbelPower
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeWaveLimits

/-! # The Abel remainder is negligible at the full power-over-log scale -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter

theorem primeClassAbel_sqrt_bound (P : Set Nat) (b C x : Real)
    (hb : 0 < b) (hC : 0 <= C) (hx : 4 <= x)
    (hmass : forall t : Real, 2 <= t -> primeClassThetaReal P t <= C * t ^ b) :
    intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
        2 x MeasureTheory.volume <=
      (C / (b * (Real.log 2) ^ 2)) * x ^ (b / 2) +
        (4 * C / b) * x ^ b / (Real.log x) ^ 2 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hfour : Real.sqrt (4 : Real) = 2 := by
    rw [show (4 : Real) = (2 : Real) ^ 2 by norm_num, Real.sqrt_sq_eq_abs,
      abs_of_pos (show (0 : Real) < 2 by norm_num)]
  have hy2 : 2 <= Real.sqrt x := by
    simpa only [hfour] using Real.sqrt_le_sqrt hx
  have hsq := Real.sq_sqrt hx0.le
  have hyx : Real.sqrt x <= x := by
    nlinarith only [hsq, hy2, sq_nonneg (Real.sqrt x - 1)]
  have hpower : (Real.sqrt x) ^ b = x ^ (b / 2) := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_mul hx0.le]
    congr 1
    ring
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hbound := primeClassAbel_two_range_bound P b C (Real.sqrt x) x hb hC hy2 hyx hmass
  rw [hpower, Real.log_sqrt hx0.le] at hbound
  calc
    _ <= C * x ^ (b / 2) / (b * (Real.log 2) ^ 2) +
        C * x ^ b / (b * (Real.log x / 2) ^ 2) := hbound
    _ = _ := by field_simp <;> ring

theorem primeClassAbel_normalized_tendsto_zero (P : Set Nat) (b C : Real)
    (hb : 0 < b) (hC : 0 <= C)
    (hmass : forall t : Real, 2 <= t -> primeClassThetaReal P t <= C * t ^ b) :
    Tendsto (fun x : Real =>
      (intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
        2 x MeasureTheory.volume) * Real.log x / x ^ b) atTop (nhds 0) := by
  have hlow := (primeWave_log_div_power_tendsto (b / 2) (by linarith only [hb])).const_mul
    (C / (b * (Real.log 2) ^ 2))
  have hhigh := Real.tendsto_log_atTop.const_div_atTop (4 * C / b)
  have hmajorant : Tendsto (fun x : Real =>
      (C / (b * (Real.log 2) ^ 2)) * (Real.log x / x ^ (b / 2)) +
        (4 * C / b) / Real.log x) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using hlow.add hhigh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajorant
  case hgf =>
    filter_upwards [eventually_ge_atTop (4 : Real)] with x hx
    have hx2 : 2 <= x := by linarith only [hx]
    have hI := primeClassAbel_integral_nonneg P 2 x (le_refl _) hx2
    have hl : 0 <= Real.log x := Real.log_nonneg (by linarith only [hx])
    exact div_nonneg (mul_nonneg hI hl) (Real.rpow_nonneg (by linarith only [hx]) b)
  case hfh =>
    filter_upwards [eventually_ge_atTop (4 : Real)] with x hx
    have hx0 : 0 < x := by linarith only [hx]
    have hl : 0 < Real.log x := Real.log_pos (by linarith only [hx])
    have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
    have hhalf : 0 < x ^ (b / 2) := Real.rpow_pos_of_pos hx0 (b / 2)
    have hbound := primeClassAbel_sqrt_bound P b C x hb hC hx hmass
    have hmul := mul_le_mul_of_nonneg_right hbound hl.le
    have hdiv := div_le_div_of_nonneg_right hmul hxb.le
    have hpower : x ^ b = x ^ (b / 2) * x ^ (b / 2) := by
      rw [<- Real.rpow_add hx0]
      congr 1
      ring
    calc
      _ <= (((C / (b * (Real.log 2) ^ 2)) * x ^ (b / 2) +
          (4 * C / b) * x ^ b / (Real.log x) ^ 2) * Real.log x) / x ^ b := hdiv
      _ = _ := by
        rw [hpower]
        field_simp <;> ring

end PrimeFactorOscillations.PrimeClassDeletion
