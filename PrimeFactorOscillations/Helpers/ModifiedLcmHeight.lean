/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ModifiedLcmArithmetic

/-!
# The leading logarithmic-height cost of the actual modified LCM

The prime number theorem and the exact prime-power squeeze imply that
(log M_N - theta(N))/sqrt(N) tends to sqrt(2). No RH assumption is used.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Asymptotics

theorem lcm_psi_isEquivalent_id :
    Asymptotics.IsEquivalent atTop Chebyshev.psi (fun x : Real => x) := by
  have hsqrtBase : Asymptotics.IsLittleO atTop
      (fun _ : Real => (1 : Real)) Real.sqrt := by
    have hsqrtFunction : Real.sqrt =
        (fun x : Real => x ^ ((1 : Real) / 2)) := by
      funext x
      exact Real.sqrt_eq_rpow x
    rw [hsqrtFunction]
    simpa only [Real.rpow_zero] using
      isLittleO_log_rpow_rpow_atTop (0 : Real)
        (by norm_num : (0 : Real) < 1 / 2)
  have hsqrtProduct := hsqrtBase.mul_isBigO (Asymptotics.isBigO_refl Real.sqrt atTop)
  have hsqrt : Asymptotics.IsLittleO atTop Real.sqrt (fun x : Real => x) := by
    apply hsqrtProduct.congr'
    . filter_upwards [] with x
      simp
    . filter_upwards [eventually_ge_atTop (0 : Real)] with x hx
      simp only [Real.mul_self_sqrt hx]
  have hdiff := Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt
  have htheta := primeProfile_theta_isEquivalent_id
  change Asymptotics.IsLittleO atTop
    (Chebyshev.theta - (fun x : Real => x)) (fun x : Real => x) at htheta
  change Asymptotics.IsLittleO atTop
    (Chebyshev.psi - (fun x : Real => x)) (fun x : Real => x)
  apply (hdiff.add htheta).congr'
  . filter_upwards [] with x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  . exact Filter.EventuallyEq.refl _ _

theorem tendsto_lcm_psi_root_ratio (r : Real) (hr : 0 < r) :
    Tendsto (fun x : Real => Chebyshev.psi (x ^ r) / x ^ r)
      atTop (nhds (1 : Real)) := by
  have hRoot := tendsto_rpow_atTop hr
  exact (Asymptotics.isEquivalent_iff_tendsto_one
    (hRoot.eventually_ne_atTop 0)).mp (lcm_psi_isEquivalent_id.comp_tendsto hRoot)

theorem tendsto_lcm_psi_small_root (r : Real) (hr : 0 < r) (hrHalf : r < 1 / 2) :
    Tendsto (fun x : Real => Chebyshev.psi (x ^ r) / x ^ (1 / 2 : Real))
      atTop (nhds (0 : Real)) := by
  have h := (tendsto_lcm_psi_root_ratio r hr).mul
    (tendsto_rpow_neg_atTop (sub_pos.mpr hrHalf))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  have hPow : x ^ r * x ^ ((1 / 2 : Real) - r) = x ^ (1 / 2 : Real) := by
    rw [<- Real.rpow_add hx]
    congr 1
    ring
  rw [Real.rpow_neg hx.le, <- div_eq_mul_inv, div_div, hPow]

theorem tendsto_lcm_psi_sub_theta_div_sqrt :
    Tendsto (fun x : Real => (Chebyshev.psi x - Chebyshev.theta x) / x ^ (1 / 2 : Real))
      atTop (nhds (1 : Real)) := by
  have hTwo := tendsto_lcm_psi_root_ratio (1 / 2) (by norm_num)
  have hThree := tendsto_lcm_psi_small_root (1 / 3) (by norm_num) (by norm_num)
  have hFive := tendsto_lcm_psi_small_root (1 / 5) (by norm_num) (by norm_num)
  have hUpper := (hTwo.add hThree).add hFive
  simp only [add_zero] at hUpper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hTwo hUpper
  . filter_upwards [eventually_ge_atTop (0 : Real)] with x hx
    have hL := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hx
    have hNonneg3 := Chebyshev.psi_nonneg (x ^ (Inv.inv (3 : Real)))
    have hNonneg7 := Chebyshev.psi_nonneg (x ^ (Inv.inv (7 : Real)))
    have hPoint : Chebyshev.psi (x ^ (1 / 2 : Real)) <=
        Chebyshev.psi x - Chebyshev.theta x := by
      norm_num only [inv_eq_one_div] at hL
      linarith only [hL, hNonneg3, hNonneg7]
    exact div_le_div_of_nonneg_right hPoint (Real.rpow_nonneg hx _)
  . filter_upwards [eventually_ge_atTop (0 : Real)] with x hx
    have hU := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
    norm_num only [inv_eq_one_div] at hU
    have h := div_le_div_of_nonneg_right hU (Real.rpow_nonneg hx (1 / 2 : Real))
    simpa only [add_div] using h

theorem tendsto_lcm_theta_scaled_root (c : Real) (hc : 0 < c) :
    Tendsto (fun x : Real => Chebyshev.theta ((c * x) ^ (1 / 2 : Real)) /
      x ^ (1 / 2 : Real)) atTop (nhds (c ^ (1 / 2 : Real))) := by
  have hMul : Tendsto (fun x : Real => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
  have hRoot := (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).comp hMul
  have hRatio := (Asymptotics.isEquivalent_iff_tendsto_one
    (hRoot.eventually_ne_atTop 0)).mp (primeProfile_theta_isEquivalent_id.comp_tendsto hRoot)
  have h := hRatio.mul_const (c ^ (1 / 2 : Real))
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  simp only [Function.comp_def, Pi.div_apply]
  rw [Real.mul_rpow hc.le hx.le]
  field_simp [(Real.rpow_pos_of_pos hc (1 / 2 : Real)).ne',
    (Real.rpow_pos_of_pos hx (1 / 2 : Real)).ne']

theorem tendsto_modifiedLcm_log_height :
    Tendsto (fun N : Nat =>
      (Real.log (modifiedLcm N : Real) - Chebyshev.theta (N : Real)) /
        Real.sqrt (N : Real)) atTop (nhds (Real.sqrt 2)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hPsi := tendsto_lcm_psi_sub_theta_div_sqrt.comp hn
  have hTwo := (tendsto_lcm_theta_scaled_root 2 (by norm_num)).comp hn
  have hOne := (tendsto_lcm_theta_scaled_root 1 (by norm_num)).comp hn
  have h := (hPsi.add hTwo).sub hOne
  simp only [Real.one_rpow, one_mul, add_sub_cancel_left] at h
  rw [Real.sqrt_eq_rpow]
  apply h.congr'
  filter_upwards [] with N
  rw [modifiedLcm_log_eq_psi_add_real_theta_difference]
  simp only [Function.comp_def, one_mul, Real.sqrt_eq_rpow]
  ring

end PrimeFactorOscillations
