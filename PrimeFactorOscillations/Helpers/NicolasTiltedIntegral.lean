/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasIntegralCriterion
import PrimeFactorOscillations.Helpers.NicolasTiltedKernel

/-!
# The weighted theta integral for a positive tilt

The complete improper integral differs from z times Nicolas's theta tail
by at most an explicit constant divided by x log x. Its eventual negative
sign is equivalent to RH for each fixed positive tilt.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter MeasureTheory Set Robin1984

def nicolasTiltedIntegral (z x : Real) : Real :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    nicolasThetaError t * nicolasTiltedKernel z t)

def nicolasTiltedIntegralErrorConstant (z : Real) : Real :=
  (Real.log 4 + 5) * 14 * (z + z ^ 2)

theorem nicolasTiltedIntegralErrorConstant_nonneg {z : Real} (hz : 0 <= z) :
    0 <= nicolasTiltedIntegralErrorConstant z := by
  have hlog : 0 <= Real.log 4 := Real.log_nonneg (by norm_num)
  unfold nicolasTiltedIntegralErrorConstant
  positivity

theorem nicolasTiltedIntegrand_error {z t : Real} (hz : 0 <= z) (ht : 3 <= t) :
    norm (nicolasThetaError t * (nicolasTiltedKernel z t - z * nicolasTailKernel t)) <=
      nicolasTiltedIntegralErrorConstant z / (t ^ 2 * Real.log t) := by
  have ht0 : 0 < t := by linarith
  have hl : 1 <= Real.log t :=
    ((Real.lt_log_iff_exp_lt ht0).mpr (Real.exp_one_lt_three.trans_le ht)).le
  have hlog4 : 0 <= Real.log 4 := Real.log_nonneg (by norm_num)
  have hTheta : |nicolasThetaError t| <= (Real.log 4 + 5) * t := by
    unfold nicolasThetaError
    calc
      _ <= |Chebyshev.theta t| + |t| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (Chebyshev.theta t) 0 t
      _ = Chebyshev.theta t + t := by
        rw [abs_of_nonneg (Chebyshev.theta_nonneg t), abs_of_pos ht0]
      _ <= (Real.log 4 + 5) * t := by
        have h := (Chebyshev.theta_le_psi t).trans (Chebyshev.psi_le_const_mul_self ht0.le)
        nlinarith only [h]
  have hk := nicolasTiltedKernel_error hz (by linarith : 2 <= t) hl
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    _ <= ((Real.log 4 + 5) * t) *
        (14 * (z + z ^ 2) / (t ^ 3 * Real.log t)) :=
      mul_le_mul hTheta hk (abs_nonneg _) (by positivity)
    _ = _ := by unfold nicolasTiltedIntegralErrorConstant; field_simp

theorem nicolasTiltedIntegrand_error_majorant {z x t : Real}
    (hz : 0 <= z) (hx : 3 <= x) (ht : x < t) :
    norm (nicolasThetaError t * (nicolasTiltedKernel z t - z * nicolasTailKernel t)) <=
      (nicolasTiltedIntegralErrorConstant z / Real.log x) * t ^ (-(2 : Real)) := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < t := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlt : Real.log x <= Real.log t := Real.log_le_log hx0 ht.le
  have hc := nicolasTiltedIntegralErrorConstant_nonneg hz
  calc
    _ <= nicolasTiltedIntegralErrorConstant z / (t ^ 2 * Real.log t) :=
      nicolasTiltedIntegrand_error hz (hx.trans ht.le)
    _ <= nicolasTiltedIntegralErrorConstant z / (t ^ 2 * Real.log x) :=
      div_le_div_of_nonneg_left hc (by positivity)
        (mul_le_mul_of_nonneg_left hlt (sq_nonneg t))
    _ = _ := by
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
      field_simp

theorem integrableOn_nicolasTiltedIntegral_error {z x : Real}
    (hz : 0 <= z) (hx : 3 <= x) :
    IntegrableOn (fun t : Real =>
      nicolasThetaError t * (nicolasTiltedKernel z t - z * nicolasTailKernel t)) (Ioi x) := by
  have hx0 : 0 < x := by linarith
  have hMajor := (integrableOn_Ioi_rpow_of_lt (by norm_num : -(2 : Real) < -1)
    hx0).const_mul (nicolasTiltedIntegralErrorConstant z / Real.log x)
  apply hMajor.mono'
  . have hTheta : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable
    have hMeas : Measurable (fun t : Real =>
        nicolasThetaError t * (nicolasTiltedKernel z t - z * nicolasTailKernel t)) := by
      unfold nicolasThetaError nicolasTiltedKernel nicolasTailKernel
      fun_prop
    exact hMeas.aestronglyMeasurable
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact nicolasTiltedIntegrand_error_majorant hz hx ht

theorem integrableOn_nicolasTiltedIntegral {z x : Real}
    (hz : 0 <= z) (hx : 3 <= x) :
    IntegrableOn (fun t : Real => nicolasThetaError t * nicolasTiltedKernel z t) (Ioi x) := by
  have hK := nicolasThetaTail_integrableOn_Ioi_two.mono_set
    (Ioi_subset_Ioi (show 2 <= x by linarith))
  have hCorr := integrableOn_nicolasTiltedIntegral_error hz hx
  apply (hCorr.add (hK.const_mul z)).congr_fun
  . intro t _
    dsimp
    ring
  . exact measurableSet_Ioi

theorem nicolasTiltedIntegral_sub_mul_K {z x : Real}
    (hz : 0 <= z) (hx : 3 <= x) :
    nicolasTiltedIntegral z x - z * nicolasK x =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        nicolasThetaError t * (nicolasTiltedKernel z t - z * nicolasTailKernel t)) := by
  have hK := nicolasThetaTail_integrableOn_Ioi_two.mono_set
    (Ioi_subset_Ioi (show 2 <= x by linarith))
  have hI := integrableOn_nicolasTiltedIntegral hz hx
  have hEq : (fun t : Real =>
      nicolasThetaError t * (nicolasTiltedKernel z t - z * nicolasTailKernel t)) =
      (fun t : Real => nicolasThetaError t * nicolasTiltedKernel z t -
        z * (nicolasThetaError t * nicolasTailKernel t)) := by
    funext t
    ring
  rw [hEq, integral_sub hI (hK.const_mul z), integral_const_mul]
  rfl

theorem nicolasTiltedIntegral_error {z x : Real} (hz : 0 <= z) (hx : 3 <= x) :
    |nicolasTiltedIntegral z x - z * nicolasK x| <=
      nicolasTiltedIntegralErrorConstant z / (x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hMajor := (integrableOn_Ioi_rpow_of_lt (by norm_num : -(2 : Real) < -1)
    hx0).const_mul (nicolasTiltedIntegralErrorConstant z / Real.log x)
  have hBound := norm_integral_le_of_norm_le hMajor
    (show Filter.Eventually (fun t : Real =>
      norm (nicolasThetaError t * (nicolasTiltedKernel z t - z * nicolasTailKernel t)) <=
        (nicolasTiltedIntegralErrorConstant z / Real.log x) * t ^ (-(2 : Real)))
        (ae (volume.restrict (Ioi x))) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact nicolasTiltedIntegrand_error_majorant hz hx ht)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : -(2 : Real) < -1) hx0]
    at hBound
  norm_num only [show -(2 : Real) + 1 = -1 by norm_num, div_neg, div_one, neg_neg,
    Real.rpow_neg_one, Real.norm_eq_abs] at hBound
  rw [nicolasTiltedIntegral_sub_mul_K hz hx]
  convert hBound using 1
  ring

theorem eventually_nicolasTiltedIntegral_neg_of_RH
    (hRH : RiemannHypothesis) (z : Real) (hz : 0 < z) :
    Filter.Eventually (fun x : Real => nicolasTiltedIntegral z x < 0) atTop := by
  have hMain : Filter.Eventually (fun x : Real =>
      nicolasRHUpperEnvelope x * (x ^ (1 / 2 : Real) * Real.log x) < -1) atTop :=
    tendsto_nicolasRHUpperEnvelope_scaled.eventually_lt_const
      (by linarith [robin_zero_constant_le_one_twentieth])
  have hSmall : Tendsto (fun x : Real =>
      nicolasTiltedIntegralErrorConstant z * x ^ (-(1 / 2 : Real))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_rpow_neg_atTop (by norm_num : (0 : Real) < 1 / 2))
  filter_upwards [hMain, hSmall.eventually_lt_const hz, eventually_ge_atTop (4 : Real)]
    with x hMainX hSmallX hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hs : 0 < x ^ (1 / 2 : Real) * Real.log x :=
    mul_pos (Real.rpow_pos_of_pos hx0 _) hl
  have hKUpper : nicolasK x <= nicolasRHUpperEnvelope x := by
    have h := nicolasK_add_four_div_le_RH_upper_envelope hRH hx
    have hp : 0 <= (4 : Real) / x := by positivity
    linarith only [h, hp]
  have hK : nicolasK x * (x ^ (1 / 2 : Real) * Real.log x) < -1 :=
    (mul_le_mul_of_nonneg_right hKUpper hs.le).trans_lt hMainX
  have hPower : x ^ (1 / 2 : Real) / x = x ^ (-(1 / 2 : Real)) := by
    rw [div_eq_mul_inv, <- Real.rpow_neg_one, <- Real.rpow_add hx0]
    norm_num
  have hCancel :
      (nicolasTiltedIntegralErrorConstant z / (x * Real.log x)) *
        (x ^ (1 / 2 : Real) * Real.log x) =
        nicolasTiltedIntegralErrorConstant z * x ^ (-(1 / 2 : Real)) := by
    calc
      _ = nicolasTiltedIntegralErrorConstant z * (x ^ (1 / 2 : Real) / x) := by
        field_simp
      _ = _ := by rw [hPower]
  have hError := (abs_le.mp (nicolasTiltedIntegral_error hz.le (by linarith : 3 <= x))).2
  have hScaledError := mul_le_mul_of_nonneg_right hError hs.le
  rw [hCancel] at hScaledError
  have hScaledK := mul_lt_mul_of_pos_left hK hz
  by_contra hNot
  have hNonneg := mul_nonneg (le_of_not_gt hNot) hs.le
  nlinarith only [hScaledError, hScaledK, hSmallX, hNonneg]

theorem riemannHypothesis_iff_eventually_nicolasTiltedIntegral_neg
    (z : Real) (hz : 0 < z) :
    RiemannHypothesis <-> Filter.Eventually
      (fun x : Real => nicolasTiltedIntegral z x < 0) atTop := by
  constructor
  . intro hRH
    exact eventually_nicolasTiltedIntegral_neg_of_RH hRH z hz
  . intro hEvent
    by_contra hNotRH
    choose X hX using eventually_atTop.mp hEvent
    let C := nicolasTiltedIntegralErrorConstant z
    have hC : 0 <= C := nicolasTiltedIntegralErrorConstant_nonneg hz.le
    choose x hx hSupply using
      nicolasK_scaled_positive_supply_of_not_RH hNotRH (C / z + 1) (max X 3)
    have hx3 : 3 <= x := (le_max_right X 3).trans hx
    have hx0 : 0 < x := by linarith
    have hl : 1 <= Real.log x :=
      ((Real.lt_log_iff_exp_lt hx0).mpr (Real.exp_one_lt_three.trans_le hx3)).le
    have hError := (abs_le.mp (nicolasTiltedIntegral_error hz.le hx3)).1
    have hAllow : x * (C / (x * Real.log x)) <= C := by
      have hCancel : x * (C / (x * Real.log x)) = C / Real.log x := by field_simp
      rw [hCancel]
      simpa only [div_one] using div_le_div_of_nonneg_left hC (by norm_num : (0 : Real) < 1) hl
    have hScaledSupply := mul_lt_mul_of_pos_left hSupply hz
    have hCancel : z * (C / z + 1) = C + z := by field_simp
    rw [hCancel] at hScaledSupply
    have hNegative := mul_neg_of_pos_of_neg hx0 (hX x ((le_max_left X 3).trans hx))
    change -(C / (x * Real.log x)) <= nicolasTiltedIntegral z x - z * nicolasK x at hError
    have hLower := mul_le_mul_of_nonneg_left hError hx0.le
    nlinarith only [hLower, hScaledSupply, hAllow, hNegative, hz]

end PrimeFactorOscillations
