/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasSpectralPsi

/-!
# Spectral atom bounds in a fixed zero-free strip

The exact cone inequality bounds the complex reciprocal zero product by its
positive real part. Its constant is used to extend the weighted Nicolas
formula from RH to a boundary b < 1. No zero-free strip is proved here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

/-- The reciprocal zero product lies in a cone controlled by the strip. -/
theorem strip_product_squared_bound
    {a b t : Real} (hLower : 1 - b <= a) (hUpper : a <= b) :
    4 * (b * (1 - b)) *
        ((a * (1 - a) + t ^ 2) ^ 2 + (t * (1 - 2 * a)) ^ 2) <=
      (a * (1 - a) + t ^ 2) ^ 2 := by
  let w := a * (1 - a)
  let u := w + t ^ 2
  let v := t * (1 - 2 * a)
  have hw : b * (1 - b) <= w := by
    have h := mul_nonneg (sub_nonneg.mpr hUpper)
      (show 0 <= a + b - 1 by linarith)
    dsimp [w]
    nlinarith only [h]
  have hFactor : u ^ 2 - 4 * w * (u ^ 2 + v ^ 2) =
      (1 - 2 * a) ^ 2 * (w - t ^ 2) ^ 2 := by
    dsimp [u, v, w]
    ring
  have hNonneg := mul_nonneg (sq_nonneg (1 - 2 * a))
    (sq_nonneg (w - t ^ 2))
  have hCompare := mul_le_mul_of_nonneg_right hw
    (show 0 <= 4 * (u ^ 2 + v ^ 2) by positivity)
  change 4 * (b * (1 - b)) * (u ^ 2 + v ^ 2) <= u ^ 2
  nlinarith only [hFactor, hNonneg, hCompare]

theorem strip_product_norm_bound {b : Real} (hb : 0 < b) (hbOne : b < 1)
    {rho : Complex} (hLower : 1 - b <= rho.re) (hUpper : rho.re <= b) :
    2 * Real.sqrt (b * (1 - b)) * norm (rho * (1 - rho)) <=
      (rho * (1 - rho)).re := by
  have hRoot : 0 <= b * (1 - b) := mul_nonneg hb.le (by linarith)
  have hRePos : 0 < rho.re := by linarith
  have hReOne : rho.re < 1 := by linarith
  have hReal : 0 <= (rho * (1 - rho)).re := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    nlinarith only [mul_nonneg hRePos.le (sub_nonneg.mpr hReOne.le),
      sq_nonneg rho.im]
  apply le_of_sq_le_sq _ hReal
  rw [mul_pow, mul_pow, Real.sq_sqrt hRoot, Complex.sq_norm]
  have h := strip_product_squared_bound (t := rho.im) hLower hUpper
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  convert h using 1 <;> ring

theorem strip_inverse_product_norm_bound {b : Real}
    (hb : 0 < b) (hbOne : b < 1) {rho : Complex}
    (hLower : 1 - b <= rho.re) (hUpper : rho.re <= b) :
    norm ((rho * (1 - rho)) ^ (-1 : Int)) <=
      ((rho * (1 - rho)) ^ (-1 : Int)).re /
        (2 * Real.sqrt (b * (1 - b))) := by
  have hRootPos : 0 < Real.sqrt (b * (1 - b)) := by positivity
  have hA : 0 < 2 * Real.sqrt (b * (1 - b)) := by positivity
  have hRho : Not (rho = 0) := by
    intro h
    simp only [h, Complex.zero_re] at hLower
    linarith
  have hOne : Not (1 - rho = 0) := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hh
    linarith
  have hProd : Not (rho * (1 - rho) = 0) := mul_ne_zero hRho hOne
  have hNorm : 0 < norm (rho * (1 - rho)) := norm_pos_iff.mpr hProd
  have hSq : 0 < Complex.normSq (rho * (1 - rho)) := by
    rw [<- Complex.sq_norm]
    positivity
  rw [zpow_neg_one, norm_inv, Complex.inv_re]
  have hLeft : (norm (rho * (1 - rho))) ^ (-1 : Int) *
      (Complex.normSq (rho * (1 - rho)) * (2 * Real.sqrt (b * (1 - b)))) =
      2 * Real.sqrt (b * (1 - b)) * norm (rho * (1 - rho)) := by
    rw [zpow_neg_one, <- Complex.sq_norm]
    field_simp
  have hRight : ((rho * (1 - rho)).re /
      Complex.normSq (rho * (1 - rho)) / (2 * Real.sqrt (b * (1 - b)))) *
      (Complex.normSq (rho * (1 - rho)) * (2 * Real.sqrt (b * (1 - b)))) =
      (rho * (1 - rho)).re := by
    field_simp [hRootPos.ne']
  by_contra hNot
  have hStrict := mul_lt_mul_of_pos_right (lt_of_not_ge hNot) (mul_pos hSq hA)
  rw [hRight, <- zpow_neg_one, hLeft] at hStrict
  exact (not_lt_of_ge (strip_product_norm_bound hb hbOne hLower hUpper)) hStrict

/-- A strip boundary controls the full atom, with its complex phase retained. -/
theorem norm_nicolasSpectralAtom_strip_le {b : Real}
    (hb : 0 < b) (hbOne : b < 1) {rho : Complex}
    (hLower : 1 - b <= rho.re) (hUpper : rho.re <= b)
    {x : Real} (hx : 1 < x) :
    norm (nicolasSpectralAtom rho x) <=
      x ^ (b - 1) * (((rho * (1 - rho)) ^ (-1 : Int)).re /
        (2 * Real.sqrt (b * (1 - b)))) := by
  have hPower : x ^ (rho.re - 1) <= x ^ (b - 1) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hCone := strip_inverse_product_norm_bound hb hbOne hLower hUpper
  rw [nicolasSpectralAtom, div_eq_mul_inv, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
  simp only [Complex.sub_re, Complex.one_re]
  apply mul_le_mul hPower
  . simpa only [zpow_neg_one] using hCone
  . exact norm_nonneg _
  . exact Real.rpow_nonneg (zero_lt_one.trans hx).le _

end PrimeFactorOscillations
