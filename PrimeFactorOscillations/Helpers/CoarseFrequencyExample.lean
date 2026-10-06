/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileWindowBands

/-!
# A full double-logarithmic growth exponent need not determine density

The nonnegative real-valued model has full coarse growth exponent while its
ratio to x tends to zero. This is an abstract information-loss example;
no actual prime-gap frequency is asserted to have the modeled shape.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter

def coarseFrequencyModel (a x : Real) : Real := max (x ^ a - 3) 0

theorem coarseFrequencyModel_gauge_limit (a : Real) (ha : 0 < a) :
    Tendsto (fun x : Real =>
      Real.log (Real.log (3 + coarseFrequencyModel a x)) /
        Real.log (Real.log x)) atTop (nhds 1) := by
  have hLL : Tendsto (fun x : Real => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hSmall : Tendsto (fun x : Real => Real.log a / Real.log (Real.log x))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hLL).const_mul (Real.log a)
  have hLimit : Tendsto (fun x : Real => 1 + Real.log a / Real.log (Real.log x))
      atTop (nhds 1) := by simpa only [add_zero] using tendsto_const_nhds.add hSmall
  have he : Filter.EventuallyEq atTop
      (fun x : Real => Real.log (Real.log (3 + coarseFrequencyModel a x)) /
        Real.log (Real.log x))
      (fun x : Real => 1 + Real.log a / Real.log (Real.log x)) := by
    filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop 3,
      hLL.eventually_gt_atTop 0, eventually_gt_atTop (1 : Real)] with x hp hll hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hl : 0 < Real.log x := Real.log_pos hx
    rw [coarseFrequencyModel, max_eq_left (by linarith), add_sub_cancel,
      Real.log_rpow hx0, Real.log_mul ha.ne' hl.ne']
    field_simp
    ring
  exact (tendsto_congr' he).mpr hLimit

theorem coarseFrequencyModel_density_zero (a : Real) (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun x : Real => coarseFrequencyModel a x / x) atTop (nhds 0) := by
  have hPower : Tendsto (fun x : Real => x ^ (a - 1)) atTop (nhds 0) := by
    have ht := tendsto_rpow_neg_atTop (by linarith : 0 < 1 - a)
    simpa only [neg_sub] using ht
  have hSmall : Tendsto (fun x : Real => 3 / x) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (3 : Real)
  have he : Filter.EventuallyEq atTop
      (fun x : Real => coarseFrequencyModel a x / x)
      (fun x : Real => x ^ (a - 1) - 3 / x) := by
    filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop 3,
      eventually_gt_atTop (0 : Real)] with x hp hx
    rw [coarseFrequencyModel, max_eq_left (by linarith), sub_div, Real.rpow_sub hx, Real.rpow_one]
  apply (tendsto_congr' he).mpr
  simpa only [sub_zero] using hPower.sub hSmall

/-- A real-valued count model, not a claim that any prime-gap frequency has this shape. -/
theorem full_coarse_exponent_allows_zero_density :
    exists f : Real -> Real,
      (forall x, 0 <= f x) /\
      Tendsto (fun x : Real => Real.log (Real.log (3 + f x)) /
        Real.log (Real.log x)) atTop (nhds 1) /\
      Tendsto (fun x : Real => f x / x) atTop (nhds 0) := by
  exact Exists.intro (coarseFrequencyModel (1 / 2))
    (And.intro (fun x => le_max_right _ _)
      (And.intro (coarseFrequencyModel_gauge_limit (1 / 2) (by norm_num))
        (coarseFrequencyModel_density_zero (1 / 2) (by norm_num) (by norm_num))))

end PrimeFactorOscillations


