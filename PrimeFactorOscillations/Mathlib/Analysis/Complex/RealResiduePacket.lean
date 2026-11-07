/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.Complex.RationalResidueBudget

/-!
# Geometry and integer budgets for aggregate real residues

A global one-sided defect budget controls a signed integer level without
separating its positive and negative constituents. The height scale is
uniform over the closed real strip and independent of packet cardinality.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Complex

def realResidueHeightScale (d H : Real) : Real := d * (d - 1) ^ 2 / (d ^ 2 + H ^ 2)

theorem realResidueHeightScale_pos (d : Real) (hd : 1 < d) (H : Real) :
    0 < realResidueHeightScale d H := by
  have hd0 : 0 < d := by linarith
  have hd1 : 0 < d - 1 := by linarith
  unfold realResidueHeightScale
  apply div_pos (mul_pos hd0 (sq_pos_of_pos hd1))
  nlinarith only [sq_pos_of_pos hd0, sq_nonneg H]

theorem realPowerResidueDefect_height_lower (d : Real) (hd : 1 < d)
    (z : Complex) (hLo : 0 <= z.re) (hHi : z.re <= 1)
    (H : Real) (_hH : 0 <= H) (hHeight : abs z.im <= H) :
    realResidueHeightScale d H <= realPowerResidueDefect d z := by
  have hd0 : 0 < d := by linarith
  have hx : 0 < z.re + d - 1 := by linarith
  have hDen : 0 < (z.re + d - 1) ^ 2 + z.im ^ 2 := by
    nlinarith only [sq_pos_of_pos hx, sq_nonneg z.im]
  have hHeightBounds := abs_le.mp hHeight
  have hT := mul_nonneg (show 0 <= H - z.im by linarith only [hHeightBounds.2])
    (show 0 <= H + z.im by linarith only [hHeightBounds.1])
  have hX := mul_nonneg (show 0 <= d - (z.re + d - 1) by linarith only [hHi])
    (show 0 <= d + (z.re + d - 1) by linarith)
  have hUpper : (z.re + d - 1) ^ 2 + z.im ^ 2 <= d ^ 2 + H ^ 2 := by
    nlinarith only [hT, hX]
  have hNum := mul_nonneg (mul_nonneg hd0.le (show 0 <= d - 1 by linarith)) hLo
  have hNumLe : d * (d - 1) ^ 2 <= d * (d - 1) * (z.re + d - 1) := by
    nlinarith only [hNum]
  rw [realPowerResidueDefect_formula d hd z hLo]
  unfold realResidueHeightScale
  exact (div_le_div_of_nonneg_left (mul_nonneg hd0.le (sq_nonneg _)) hDen hUpper).trans
    (div_le_div_of_nonneg_right hNumLe hDen.le)

theorem inverse_product_re_nonneg (z : Complex) (hLo : 0 <= z.re) (hHi : z.re <= 1) :
    0 <= ((z * (1 - z)) ^ (-1 : Int)).re := by
  rw [zpow_neg_one, Complex.inv_re]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  have h := mul_nonneg hLo (sub_nonneg.mpr hHi)
  nlinarith only [h, sq_nonneg z.im]

theorem inverse_re_le_inverse_product_re (z : Complex) (hLo : 0 < z.re) (hHi : z.re < 1) :
    (Inv.inv z).re <= ((z * (1 - z)) ^ (-1 : Int)).re := by
  have hz : Not (z = 0) := by intro h; simp [h] at hLo
  have ho : Not (1 - z = 0) := by
    intro h
    have hr := congrArg Complex.re (sub_eq_zero.mp h)
    simp only [Complex.one_re] at hr
    linarith only [hHi, hr]
  have he : (z * (1 - z)) ^ (-1 : Int) = Inv.inv z + Inv.inv (1 - z) := by
    rw [zpow_neg_one]
    field_simp
    ring
  have hp : 0 <= (Inv.inv (1 - z)).re := by
    rw [Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hHi]
  rw [he, Complex.add_re]
  linarith only [hp]

end Complex
namespace Real

theorem integer_sub_budget_zero (i : Int) (u c : Real)
    (hu : 0 <= u) (huc : u <= c) (hc : c < 1)
    (hZero : (i : Real) - u = 0) : And (i = 0) (u = 0) := by
  have hlo : (0 : Real) <= i := by linarith only [hu, hZero]
  have hhi : (i : Real) < 1 := by linarith only [huc, hc, hZero]
  have hi0 : (0 : Int) <= i := by exact_mod_cast hlo
  have hi1 : i < (1 : Int) := by exact_mod_cast hhi
  have hi : i = 0 := by omega
  refine And.intro hi ?_
  rw [hi, Int.cast_zero, zero_sub] at hZero
  exact neg_eq_zero.mp hZero

theorem integer_sub_budget_abs_lower (i : Int) (u c ell : Real)
    (hu : 0 <= u) (huc : u <= c) (hc : c < 1)
    (hAtZero : i = 0 -> ell <= u) :
    min (1 - c) ell <= abs ((i : Real) - u) := by
  by_cases hi : i = 0
  . rw [hi, Int.cast_zero, zero_sub, abs_neg, abs_of_nonneg hu]
    exact (min_le_right _ _).trans (hAtZero hi)
  . by_cases hip : 0 < i
    . have hiOne : (1 : Int) <= i := by omega
      have hiR : (1 : Real) <= i := by exact_mod_cast hiOne
      have hSign : 0 <= (i : Real) - u := by linarith only [hiR, huc, hc]
      rw [abs_of_nonneg hSign]
      exact (min_le_left _ _).trans (by linarith only [hiR, huc])
    . have hiOne : i <= (-1 : Int) := by omega
      have hiR : (i : Real) <= -1 := by exact_mod_cast hiOne
      have hc0 : 0 <= c := hu.trans huc
      have hSign : (i : Real) - u <= 0 := by linarith only [hiR, hu]
      rw [abs_of_nonpos hSign]
      exact (min_le_left _ _).trans (by linarith only [hiR, hu, hc0])

theorem integer_sub_budget_index (i : Int) (u c y : Real)
    (hu : 0 <= u) (huc : u <= c)
    (hNoise : abs ((i : Real) - u - y) < (1 - c) / 2) :
    scalarBudgetInteger c y = i := by
  have h := scalarBudgetInteger_eq 0 (-i) 1 c u y
    (by simpa using And.intro hu huc) (by simpa using hNoise)
  simpa using h

end Real
