/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import PrimeFactorOscillations.Assembly.CarmichaelSharpMultiplicity
import PrimeFactorOscillations.Helpers.XiThreeLineMultiplicity

/-! # A strict three-line improvement of the global multiplicity coefficient

The installed unconditional seven-eighths strip is an input. The new result
improves the multiplicity coefficient, not the zero-free boundary. The fixed
explicit additive constant is not a claim of a larger numerical simplicity
window.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

theorem threeLineMultiplicityConstant_nonneg : 0 <= threeLineMultiplicityConstant := by
  let a : Real := 1 / 2 + threeLineRadius1
  have ha : 1 < a := by norm_num [a, threeLineRadius1]
  have hH : 0 <= threeLineHeightConstant := xiExplicitHeight_nonneg a a ha
  have hL : 0 <= threeLineLipschitzConstant := xiExplicitLipschitz_nonneg a ha
  have hR : 0 <= threeLineRemainderScale := by unfold threeLineRemainderScale; positivity
  have hS : 0 <= threeLineWeight1 + threeLineWeight2 + threeLineWeight3 := by
    norm_num [threeLineWeight1, threeLineWeight2, threeLineWeight3]
  unfold threeLineMultiplicityConstant
  exact div_nonneg (add_nonneg (mul_nonneg hS hH) (mul_nonneg hL hR)) threeLineCharge_pos.le

theorem threeLine_rational_lt_twoLine_optimum :
    (1321 / 10000 : Real) < Real.sharpResolventCoefficient := by
  have h7sq : (Real.sqrt (7 : Real)) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h7n : 0 <= Real.sqrt (7 : Real) := Real.sqrt_nonneg _
  have h7u : Real.sqrt (7 : Real) < 53 / 20 := by nlinarith only [h7sq, h7n]
  have hd : 0 <= (13 - 3 * Real.sqrt 7 : Real) := by linarith only [h7u]
  let z : Real := Real.sqrt (13 - 3 * Real.sqrt 7)
  have hzsq : z ^ 2 = 13 - 3 * Real.sqrt 7 := Real.sq_sqrt hd
  have hzn : 0 <= z := Real.sqrt_nonneg _
  have hzlo : (2642 / 1179 : Real) < z := by nlinarith only [hzsq, h7u, hzn]
  have hden : 0 < 4 * (2 + z) := by positivity
  change (1321 / 10000 : Real) < z / (4 * (2 + z))
  apply (mul_lt_mul_iff_of_pos_right hden).mp
  have he : z / (4 * (2 + z)) * (4 * (2 + z)) = z := by field_simp [hden.ne']
  rw [he]
  nlinarith only [hzlo]

theorem threeLineLeadingCoefficient_lt_twoLine_optimum :
    threeLineLeadingCoefficient < Real.sharpResolventCoefficient :=
  threeLineLeadingCoefficient_lt.trans threeLine_rational_lt_twoLine_optimum

theorem zeta_multiplicity_threeLine_log_bound {w : Complex}
    (hw : And (0 < w.re) (w.re < 1)) (ht : 2 <= abs w.im) :
    (analyticOrderNatAt riemannZeta w : Real) <=
      threeLineLeadingCoefficient * Real.log (abs w.im) + threeLineMultiplicityConstant :=
  zeta_multiplicity_le_threeLine_bound hw ht xi_seven_eighths_centered_strip

theorem zeta_multiplicity_threeLine_rational_log_bound {w : Complex}
    (hw : And (0 < w.re) (w.re < 1)) (ht : 2 <= abs w.im) :
    (analyticOrderNatAt riemannZeta w : Real) <=
      (1321 / 10000 : Real) * Real.log (abs w.im) + threeLineMultiplicityConstant := by
  have hh := zeta_multiplicity_threeLine_log_bound hw ht
  have hlog : 0 <= Real.log (abs w.im) := Real.log_nonneg (by linarith only [ht])
  have hl := mul_le_mul_of_nonneg_right threeLineLeadingCoefficient_lt.le hlog
  linarith only [hh, hl]

end PrimeFactorOscillations
