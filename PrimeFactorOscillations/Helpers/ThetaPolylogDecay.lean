/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThetaErrorIntegrability

/-!
# Unconditional theta error at every fixed logarithmic power

Uses the pinned quantitative prime number theorem and the elementary prime-power
difference. This supplies the unconditional error input for the smaller growing
consecutive-root family; no Riemann hypothesis is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Filter Real Asymptotics
namespace PrimeFactorOscillations

theorem tendsto_log_pow_div_sqrt (m : Nat) :
    Tendsto (fun x : Real => Real.log x ^ (m + 1) / Real.sqrt x)
      atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_atTop
    (show (0 : Real) < 1 / (2 * ((m : Real) + 1)) by positivity)).pow
      (n := m + 1) (by omega)
  have heq : Filter.EventuallyEq atTop
      (fun x : Real => (x ^ (1 / (2 * ((m : Real) + 1)))) ^ (m + 1))
      (fun x : Real => Real.sqrt x) := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hx.le, Real.sqrt_eq_rpow]
    congr 1
    push_cast
    field_simp
  exact (h.congr' Filter.EventuallyEq.rfl heq).tendsto_div_nhds_zero

theorem thetaError_isBigO_div_log_pow (m : Nat) :
    IsBigO atTop (fun x : Real => Chebyshev.theta x - x)
      (fun x : Real => x / Real.log x ^ m) := by
  choose c hc hPNT using MediumPNT
  change IsBigO atTop (Chebyshev.psi - id)
    (fun x : Real => x * Real.exp (-c * Real.log x ^ (1 / 10 : Real))) at hPNT
  have hDecay : Tendsto
      (fun x : Real => Real.exp (-c * Real.log x ^ (1 / 10 : Real)) *
        Real.log x ^ m) atTop (nhds 0) := by
    have hz : Tendsto (fun z : Real =>
        Real.exp (-z) * (z / c) ^ (10 * m)) atTop (nhds 0) := by
      convert (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (10 * m)).div_const
        (c ^ (10 * m)) using 2 <;> ring
    have hy : Tendsto (fun y : Real => Real.exp (-c * y) * y ^ (10 * m))
        atTop (nhds 0) := by
      convert hz.comp (tendsto_id.const_mul_atTop hc) using 2
      norm_num [hc.ne']
    have hs := hy.comp
      ((tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 10)).comp
        Real.tendsto_log_atTop)
    apply hs.congr'
    filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
    have heq : (Real.log x ^ (1 / 10 : Real)) ^ (10 * m) =
        Real.log x ^ m := by
      rw [<- Real.rpow_natCast, <- Real.rpow_mul (Real.log_nonneg hx.le),
        <- Real.rpow_natCast]
      congr 1
      push_cast
      ring
    simpa only [Function.comp_def, heq]
  have hExp : IsBigO atTop
      (fun x : Real => Real.exp (-c * Real.log x ^ (1 / 10 : Real)))
      (fun x : Real => 1 / Real.log x ^ m) := by
    apply IsBigO.of_bound 1
    filter_upwards [hDecay.eventually_lt_const (by norm_num : (0 : Real) < 1),
      eventually_gt_atTop (1 : Real)] with x hx hxOne
    have hl : 0 < Real.log x := Real.log_pos hxOne
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_div,
      norm_one, norm_pow, Real.norm_eq_abs, abs_of_pos hl, one_mul]
    calc
      _ = (Real.exp (-c * Real.log x ^ (1 / 10 : Real)) * Real.log x ^ m) *
          (1 / Real.log x ^ m) := by field_simp
      _ <= 1 * (1 / Real.log x ^ m) :=
        mul_le_mul_of_nonneg_right hx.le (by positivity)
      _ = _ := by ring
  have hPsi : IsBigO atTop (Chebyshev.psi - id)
      (fun x : Real => x / Real.log x ^ m) := by
    apply hPNT.trans
    convert (isBigO_refl (fun x : Real => x) atTop).mul hExp using 2 <;> ring
  have hDiff : IsBigO atTop (fun x : Real => Chebyshev.theta x - Chebyshev.psi x)
      (fun x : Real => x / Real.log x ^ m) := by
    apply IsBigO.of_bound 2
    filter_upwards [(tendsto_log_pow_div_sqrt m).eventually_lt_const
      (by norm_num : (0 : Real) < 1), eventually_gt_atTop (1 : Real)] with x hRatio hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hl : 0 < Real.log x := Real.log_pos hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hProduct := mul_le_mul_of_nonneg_right hRatio.le hs.le
    have hCancel : (Real.log x ^ (m + 1) / Real.sqrt x) * Real.sqrt x =
        Real.log x ^ (m + 1) := by field_simp
    rw [hCancel, one_mul] at hProduct
    have hScaled := mul_le_mul_of_nonneg_left hProduct
      (show 0 <= 2 * Real.sqrt x by positivity)
    have hSqrt : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hMain : 2 * Real.sqrt x * Real.log x <= 2 * x / Real.log x ^ m := by
      apply (mul_le_mul_iff_of_pos_right (pow_pos hl m)).mp
      have hCancel' : (2 * x / Real.log x ^ m) * Real.log x ^ m = 2 * x := by
        field_simp
      rw [hCancel']
      rw [pow_succ] at hScaled
      nlinarith only [hScaled, hSqrt]
    simp only [Real.norm_eq_abs, norm_div, norm_pow, abs_of_pos hx0,
      abs_of_pos hl, mul_div]
    have hBound : abs (Chebyshev.theta x - Chebyshev.psi x) <=
        2 * Real.sqrt x * Real.log x := by
      rw [<- neg_sub, abs_neg]
      exact Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx.le
    exact hBound.trans hMain
  have hSum := hPsi.add hDiff
  convert hSum using 1
  funext x
  simp only [Pi.sub_apply, id_eq]
  ring

end PrimeFactorOscillations
