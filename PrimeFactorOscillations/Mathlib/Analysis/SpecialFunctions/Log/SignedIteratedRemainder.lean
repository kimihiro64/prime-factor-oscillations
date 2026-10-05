/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.IteratedRemainder

/-!
# Signed quadratic error for log log

The tangent error is controlled on both sides of the base point. The
negative-displacement case keeps the cancellation between the two slopes.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Real

theorem logLog_remainder_bounds_of_le
    {x y : Real} (hy : 1 < y) (hyx : y <= x) (hxy : x <= 2 * y)
    (hLy : 1 <= log y) :
    0 <= (y - x) / (x * log x) - (log (log y) - log (log x)) /\
    (y - x) / (x * log x) - (log (log y) - log (log x)) <=
      6 * (y - x) ^ 2 / (x ^ 2 * log x) := by
  have hx : 1 < x := hy.trans_le hyx
  have hyPos : 0 < y := by linarith
  have hxPos : 0 < x := by linarith
  have hLx : 0 < log x := log_pos hx
  have hly : 0 < log y := log_pos hy
  have hsecant {a b : Real} (ha : 0 < a) (hb : 0 < b) :
      log a - log b <= (a - b) / b := by
    calc
      _ = log (a / b) := (log_div ha.ne' hb.ne').symm
      _ <= a / b - 1 := log_le_sub_one_of_pos (div_pos ha hb)
      _ = _ := by field_simp
  have hOuter := hsecant hly hLx
  have hInner := (div_le_div_iff_of_pos_right hLx).2 (hsecant hyPos hxPos)
  have hDnonneg :
      0 <= (y - x) / (x * log x) - (log (log y) - log (log x)) := by
    have heq : ((y - x) / x) / log x = (y - x) / (x * log x) := by ring
    rw [heq] at hInner
    linarith only [hOuter, hInner]
  refine And.intro hDnonneg ?_
  let F := x - y
  let a := Inv.inv x
  let b := Inv.inv y
  let r := Inv.inv (log x)
  let s := Inv.inv (log y)
  have hF : 0 <= F := sub_nonneg.mpr hyx
  have ha : 0 <= a := (inv_pos.mpr hxPos).le
  have hb : 0 <= b := (inv_pos.mpr hyPos).le
  have hr : 0 <= r := (inv_pos.mpr hLx).le
  have hs : 0 <= s := (inv_pos.mpr hly).le
  have hs1 : s <= 1 := by
    dsimp [s]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hLy
  have hb2a : b <= 2 * a := by
    have h := one_div_le_one_div_of_le (show 0 < x / 2 by positivity)
      (show x / 2 <= y by linarith)
    dsimp [a, b]
    convert h using 1 <;> field_simp
  have hLogs : log x - log y <= F * b := by
    simpa only [F, b, div_eq_mul_inv] using hsecant hxPos hyPos
  have hReverseOuter := hsecant hLx hly
  have hReverseInner := (div_le_div_iff_of_pos_right hly).2 (hsecant hxPos hyPos)
  have hDupper :
      (y - x) / (x * log x) - (log (log y) - log (log x)) <=
        F * (b * s - a * r) := by
    have heq : (x - y) / y / log y + (y - x) / (x * log x) =
        F * (b * s - a * r) := by
      dsimp [F, a, b, r, s]
      field_simp
      ring
    linarith only [hReverseOuter, hReverseInner, heq]
  have hExact : b * s - a * r =
      F * a * b * r + (log x - log y) * b * r * s := by
    dsimp [F, a, b, r, s]
    field_simp
    ring
  have hLogPart := mul_le_mul_of_nonneg_right hLogs
    (show 0 <= b * r * s by positivity)
  have hGap : b * s - a * r <= F * (a * b + b ^ 2 * s) * r := by
    nlinarith only [hExact, hLogPart]
  have hab := mul_le_mul_of_nonneg_left hb2a ha
  have hbsq : b ^ 2 <= 4 * a ^ 2 := by nlinarith only [ha, hb, hb2a]
  have hsquare := mul_le_mul_of_nonneg_left hs1 (sq_nonneg b)
  have hCoefficient : a * b + b ^ 2 * s <= 6 * a ^ 2 := by
    nlinarith only [hab, hbsq, hsquare]
  have hScale := mul_le_mul_of_nonneg_left hCoefficient
    (show 0 <= F * r by positivity)
  have hGapFinal : b * s - a * r <= 6 * F * a ^ 2 * r := by
    nlinarith only [hGap, hScale]
  have hFinal := mul_le_mul_of_nonneg_left hGapFinal hF
  have hTarget : F * (6 * F * a ^ 2 * r) = 6 * (y - x) ^ 2 / (x ^ 2 * log x) := by
    dsimp [F, a, r]
    field_simp
    ring
  rw [hTarget] at hFinal
  exact hDupper.trans hFinal

theorem logLog_remainder_abs_le
    {x y : Real} (hx : 1 < x) (hy : 1 < y)
    (hLx : 1 <= log x) (hLy : 1 <= log y) (hxy : x <= 2 * y) :
    abs ((y - x) / (x * log x) - (log (log y) - log (log x))) <=
      6 * (y - x) ^ 2 / (x ^ 2 * log x) := by
  by_cases hyx : y <= x
  . have h := logLog_remainder_bounds_of_le hy hyx hxy hLy
    rw [abs_of_nonneg h.1]
    exact h.2
  . have hE : 0 <= y - x := by linarith
    have h := logLog_remainder_bounds x (y - x) hx hE
    rw [show x + (y - x) = y by ring] at h
    rw [abs_of_nonneg h.1]
    have hxPos : 0 < x := by linarith
    have hLogPos : 0 < log x := log_pos hx
    have hden : 0 < 2 * x ^ 2 * (log x) ^ 2 := by positivity
    have hCoef : (log x + 1) / (2 * x ^ 2 * (log x) ^ 2) <=
        1 / (x ^ 2 * log x) := by
      calc
        _ <= (2 * log x) / (2 * x ^ 2 * (log x) ^ 2) :=
          (div_le_div_iff_of_pos_right hden).2 (by linarith)
        _ = _ := by field_simp
    have hProd := mul_le_mul_of_nonneg_right hCoef (sq_nonneg (y - x))
    have hNonneg : 0 <= (y - x) ^ 2 / (x ^ 2 * log x) := by positivity
    calc
      _ <= 1 / (x ^ 2 * log x) * (y - x) ^ 2 := h.2.trans hProd
      _ = (y - x) ^ 2 / (x ^ 2 * log x) := by ring
      _ <= 6 * ((y - x) ^ 2 / (x ^ 2 * log x)) := by linarith only [hNonneg]
      _ = _ := by ring

end Real
