/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.NormalizedLinearProduct

/-!
# Quadratic remainders for iterated logarithms

Two elementary one-add-log remainder bounds control the exact log-log
correction for every nonnegative displacement. A logarithmic displacement
then has a remainder bounded by a constant times log x / x squared.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Real

/-- The nested logarithmic correction has a global quadratic remainder on the
nonnegative half-line. No smallness condition on `a` is required. -/
theorem div_sub_log_one_add_log_bounds
    (a L : Real) (ha : 0 <= a) (hL : 0 < L) :
    0 <= a / L - log (1 + log (1 + a) / L) /\
      a / L - log (1 + log (1 + a) / L) <=
        (L + 1) * a ^ 2 / (2 * L ^ 2) := by
  let t : Real := log (1 + a)
  have ht : 0 <= t := by
    exact log_nonneg (by linarith)
  have hFirst := sub_log_one_add_bounds a ha
  have hta : t <= a := by
    dsimp [t]
    linarith [hFirst.1]
  have hRatio : 0 <= t / L := div_nonneg ht hL.le
  have hSecond := sub_log_one_add_bounds (t / L) hRatio
  have hRatioUpper : t / L <= a / L :=
    (div_le_div_iff_of_pos_right hL).2 hta
  have hSquare : (t / L) ^ 2 <= (a / L) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hRatioUpper)
      (add_nonneg (div_nonneg ha hL.le) hRatio)
    nlinarith
  have hFirstLower : 0 <= (a - t) / L :=
    div_nonneg (sub_nonneg.mpr hta) hL.le
  have hFirstUpper : (a - t) / L <= (a ^ 2 / 2) / L := by
    exact (div_le_div_iff_of_pos_right hL).2 hFirst.2
  have hSplit : a / L - log (1 + log (1 + a) / L) =
      (a - t) / L + (t / L - log (1 + t / L)) := by
    dsimp [t]
    ring
  have hUpperIdentity : (a ^ 2 / 2) / L + (a / L) ^ 2 / 2 =
      (L + 1) * a ^ 2 / (2 * L ^ 2) := by
    field_simp [hL.ne']
  rw [hSplit]
  constructor
  . exact add_nonneg hFirstLower hSecond.1
  . calc
      (a - t) / L + (t / L - log (1 + t / L)) <=
          (a ^ 2 / 2) / L + (a / L) ^ 2 / 2 := by
        linarith [hSecond.2]
      _ = (L + 1) * a ^ 2 / (2 * L ^ 2) := hUpperIdentity

/-- Exact `log log` remainder for a nonnegative displacement. -/
theorem logLog_remainder_bounds
    (x E : Real) (hx : 1 < x) (hE : 0 <= E) :
    0 <= E / (x * log x) - (log (log (x + E)) - log (log x)) /\
      E / (x * log x) - (log (log (x + E)) - log (log x)) <=
        (log x + 1) / (2 * x ^ 2 * (log x) ^ 2) * E ^ 2 := by
  have hxPos : 0 < x := lt_trans zero_lt_one hx
  have hL : 0 < log x := log_pos hx
  have ha : 0 <= E / x := div_nonneg hE hxPos.le
  have hOne : 0 < 1 + E / x := by linarith
  have hLogOne : 0 <= log (1 + E / x) := log_nonneg (by linarith)
  have hTwo : 0 < 1 + log (1 + E / x) / log x := by
    have hRatio := div_nonneg hLogOne hL.le
    linarith
  have hAdd : x + E = x * (1 + E / x) := by
    field_simp [hxPos.ne']
  have hLogAdd : log (x + E) = log x + log (1 + E / x) := by
    rw [hAdd, log_mul hxPos.ne' hOne.ne']
  have hProduct : log x + log (1 + E / x) =
      log x * (1 + log (1 + E / x) / log x) := by
    field_simp [hL.ne']
  have hLogLog : log (log (x + E)) - log (log x) =
      log (1 + log (1 + E / x) / log x) := by
    rw [hLogAdd, hProduct, log_mul hL.ne' hTwo.ne']
    ring
  have hRemainder : E / (x * log x) -
      (log (log (x + E)) - log (log x)) =
      (E / x) / log x - log (1 + log (1 + E / x) / log x) := by
    rw [hLogLog]
    ring
  have hUpperIdentity : (log x + 1) * (E / x) ^ 2 / (2 * (log x) ^ 2) =
      (log x + 1) / (2 * x ^ 2 * (log x) ^ 2) * E ^ 2 := by
    field_simp [hxPos.ne', hL.ne']
  rw [hRemainder]
  constructor
  . exact (div_sub_log_one_add_log_bounds (E / x) (log x) ha hL).1
  . exact (div_sub_log_one_add_log_bounds (E / x) (log x) ha hL).2.trans_eq
      hUpperIdentity

/-- A logarithmic displacement gives a remainder of order `log x / x^2`. -/
theorem logLog_remainder_le_of_displacement_le_log
    (x E B : Real) (hx : 1 < x) (hE : 0 <= E) (hB : 0 <= B)
    (hUpper : E <= B * log x) :
    E / (x * log x) - (log (log (x + E)) - log (log x)) <=
      B ^ 2 * (log x + 1) / (2 * x ^ 2) := by
  have hxPos : 0 < x := lt_trans zero_lt_one hx
  have hL : 0 < log x := log_pos hx
  have hSquare : E ^ 2 <= (B * log x) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hUpper)
      (add_nonneg (mul_nonneg hB hL.le) hE)
    nlinarith
  have hCoefficient : 0 <= (log x + 1) / (2 * x ^ 2 * (log x) ^ 2) := by
    positivity
  calc
    E / (x * log x) - (log (log (x + E)) - log (log x)) <=
        (log x + 1) / (2 * x ^ 2 * (log x) ^ 2) * E ^ 2 :=
      (logLog_remainder_bounds x E hx hE).2
    _ <= (log x + 1) / (2 * x ^ 2 * (log x) ^ 2) * (B * log x) ^ 2 :=
      mul_le_mul_of_nonneg_left hSquare hCoefficient
    _ = B ^ 2 * (log x + 1) / (2 * x ^ 2) := by
      field_simp [hxPos.ne', hL.ne']

end Real
