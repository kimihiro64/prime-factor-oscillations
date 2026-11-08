/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Signed quadratic control identities and their cross comparison. -/

/-
Symbolic audit of the old-packet covariance cancellation.
This checks universal algebra, not any finite orbit sample or growth theorem.
Normalized interpretations require positive denominators as in the paper note.
-/
set_option autoImplicit false
set_option Elab.async false

namespace Real

theorem control_square_identity
    (mu nu v w c alpha : Real) :
    (mu ^ 2 * w - 2 * mu * nu * c + nu ^ 2 * v) *
        (v - 2 * alpha * c + alpha ^ 2 * w) -
      (v * w - c ^ 2) * (mu - alpha * nu) ^ 2 =
      ((mu * w - nu * c) * alpha - (mu * c - nu * v)) ^ 2 := by
  ring

theorem gain_square_identity
    (mu nu v w c : Real) :
    v * (mu ^ 2 * w - 2 * mu * nu * c + nu ^ 2 * v) -
      (v * w - c ^ 2) * mu ^ 2 =
      (nu * v - mu * c) ^ 2 := by
  ring

theorem gain_cross_nonnegative
    (mu nu v w c : Real) :
    (v * w - c ^ 2) * mu ^ 2 <=
      v * (mu ^ 2 * w - 2 * mu * nu * c + nu ^ 2 * v) := by
  calc
    (v * w - c ^ 2) * mu ^ 2 <=
        (v * w - c ^ 2) * mu ^ 2 + (nu * v - mu * c) ^ 2 :=
      le_add_of_nonneg_right (sq_nonneg (nu * v - mu * c))
    _ = v * (mu ^ 2 * w - 2 * mu * nu * c + nu ^ 2 * v) := by
      ring

theorem positive_intercept_cross_identity
    (mu nu v w c : Real) :
    mu * (mu * w - nu * c) - nu * (mu * c - nu * v) =
      mu ^ 2 * w - 2 * mu * nu * c + nu ^ 2 * v := by
  ring

private theorem quadratic_tilt_small_square (x e k c s : Real)
    (hx : 0 <= x) (hk : 0 < k) (hc : 0 < c) (hs : 0 < s)
    (he : e <= k * s ^ 2 / (4 * c))
    (hTilt : forall l : Real, And (0 <= l) (l <= s) ->
      l * x <= 2 * e + k * l ^ 2 / (2 * c)) :
    c * x ^ 2 <= 4 * k * e := by
  have hsTilt := hTilt s (And.intro hs.le le_rfl)
  have hDiv : (k * s ^ 2 / (2 * c)) * (2 * c) = k * s ^ 2 := by
    field_simp [hc.ne']
  have he' := mul_le_mul_of_nonneg_right he (show 0 <= 4 * c by positivity)
  have hCancel : (k * s ^ 2 / (4 * c)) * (4 * c) = k * s ^ 2 := by
    field_simp [hc.ne']
  rw [hCancel] at he'
  have hs' := mul_le_mul_of_nonneg_right hsTilt (show 0 <= 2 * c by positivity)
  have hCap : c * x <= k * s := by
    by_contra hn
    have hP := mul_pos hs (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hs', hDiv, he', hP]
  let l := c * x / k
  have hl : And (0 <= l) (l <= s) := by
    constructor
    case left => exact div_nonneg (mul_nonneg hc.le hx) hk.le
    case right =>
      have hh := mul_le_mul_of_nonneg_right hCap (show 0 <= 1 / k by positivity)
      have hL : c * x * (1 / k) = l := by dsimp [l]; ring
      have hR : k * s * (1 / k) = s := by field_simp [hk.ne']
      rwa [hL, hR] at hh
  have ht := hTilt l hl
  have hMultiply := mul_le_mul_of_nonneg_right ht (show 0 <= 2 * c * k by positivity)
  have hLeft : (l * x) * (2 * c * k) = 2 * c ^ 2 * x ^ 2 := by
    dsimp [l]
    field_simp [hk.ne']
  have hRight : (2 * e + k * l ^ 2 / (2 * c)) * (2 * c * k) =
      4 * c * k * e + c ^ 2 * x ^ 2 := by
    dsimp [l]
    field_simp [hk.ne', hc.ne']
    ring
  rw [hLeft, hRight] at hMultiply
  by_contra hn
  have hP := mul_pos hc (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hMultiply, hP]

theorem le_piecewise_of_quadratic_tilt (x e k c s : Real)
    (hx : 0 <= x) (he : 0 <= e) (hk : 0 < k) (hc : 0 < c) (hs : 0 < s)
    (hTilt : forall l : Real, And (0 <= l) (l <= s) ->
      l * x <= 2 * e + k * l ^ 2 / (2 * c)) :
    x <= if e <= k * s ^ 2 / (4 * c) then 2 * Real.sqrt (k * e / c)
      else 2 * e / s + k * s / (2 * c) := by
  by_cases hSmall : e <= k * s ^ 2 / (4 * c)
  case pos =>
    rw [ite_eq_left hSmall]
    have hSquare := quadratic_tilt_small_square (x) e k c s hx hk hc hs hSmall hTilt
    have hQ : 0 <= k * e / c := div_nonneg (mul_nonneg hk.le he) hc.le
    have hRoot : c * (2 * Real.sqrt (k * e / c)) ^ 2 = 4 * k * e := by
      calc
        _ = 4 * c * (Real.sqrt (k * e / c)) ^ 2 := by ring
        _ = 4 * c * (k * e / c) := by rw [Real.sq_sqrt hQ]
        _ = _ := by field_simp [hc.ne']
    by_contra hn
    have hlt : 2 * Real.sqrt (k * e / c) < x := lt_of_not_ge hn
    have hP : 0 < c * (x - 2 * Real.sqrt (k * e / c)) *
        (x + 2 * Real.sqrt (k * e / c)) :=
      mul_pos (mul_pos hc (sub_pos.mpr hlt))
        (by linarith only [hlt, Real.sqrt_nonneg (k * e / c)])
    nlinarith only [hSquare, hRoot, hP]
  case neg =>
    rw [ite_eq_right hSmall]
    have ht := hTilt s (And.intro hs.le le_rfl)
    have hIdentity : s * (2 * e / s + k * s / (2 * c)) =
        2 * e + k * s ^ 2 / (2 * c) := by
      field_simp [hs.ne', hc.ne']
    have hScaled : s * x <= s * (2 * e / s + k * s / (2 * c)) := by
      rw [hIdentity]
      exact ht
    by_contra hn
    have hP := mul_pos hs (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hScaled, hP]

end Real
