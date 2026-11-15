/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrectionStability

/-! # Exact rank shifts in the first permanent correction

All denominators are proved positive. The signed numerator difference
and old-numerator compensation remain in the exact difference identity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_first_correction_rank_shift
    (N r q : Real) (hN : 4 <= N) (hr : 0 <= r) (hq : N * q = 1)
    (hSmall : r * q <= 1 / 4) :
    0 < N - r - 1 /\ 0 < N - 1 /\
    1 / (N - r - 1) <= 2 * q /\ 1 / (N - 1) <= 2 * q /\
    (1 / (N - r - 1) - 1 / (N - 1) = r / ((N - r - 1) * (N - 1))) /\
    abs (1 / (N - r - 1) - 1 / (N - 1)) <= 4 * r * q ^ 2 := by
  have hN0 : 0 < N := by linarith only [hN]
  have hq0 : 0 <= q := by nlinarith only [hq, hN0]
  have hScaled := mul_le_mul_of_nonneg_left hSmall (le_of_lt hN0)
  have hScaleEq : N * (r * q) = r := by
    calc
      _ = r * (N * q) := by ring
      _ = r := by rw [hq, mul_one]
  rw [hScaleEq] at hScaled
  have hRQuarter : 4 * r <= N := by linarith only [hScaled]
  have hNewLow : N / 2 <= N - r - 1 := by linarith only [hN, hRQuarter]
  have hOldLow : N / 2 <= N - 1 := by linarith only [hN]
  have hNewPos : 0 < N - r - 1 := by linarith only [hNewLow, hN0]
  have hOldPos : 0 < N - 1 := by linarith only [hOldLow, hN0]
  have hNewNe : Not (N - r - 1 = 0) := ne_of_gt hNewPos
  have hOldNe : Not (N - 1 = 0) := ne_of_gt hOldPos
  have hNewInv : 1 / (N - r - 1) <= 2 * q := by
    have hMul := mul_le_mul_of_nonneg_left hNewLow
      (mul_nonneg (by norm_num : (0 : Real) <= 2) hq0)
    have hOne : 1 <= (2 * q) * (N - r - 1) := by nlinarith only [hMul, hq]
    have h := mul_le_mul_of_nonneg_right hOne (le_of_lt (one_div_pos.mpr hNewPos))
    have hCancel : ((2 * q) * (N - r - 1)) * (1 / (N - r - 1)) = 2 * q := by
      field_simp [hNewNe]
    simpa only [one_mul, hCancel] using h
  have hOldInv : 1 / (N - 1) <= 2 * q := by
    have hMul := mul_le_mul_of_nonneg_left hOldLow
      (mul_nonneg (by norm_num : (0 : Real) <= 2) hq0)
    have hOne : 1 <= (2 * q) * (N - 1) := by nlinarith only [hMul, hq]
    have h := mul_le_mul_of_nonneg_right hOne (le_of_lt (one_div_pos.mpr hOldPos))
    have hCancel : ((2 * q) * (N - 1)) * (1 / (N - 1)) = 2 * q := by
      field_simp [hOldNe]
    simpa only [one_mul, hCancel] using h
  have hExact : 1 / (N - r - 1) - 1 / (N - 1) = r / ((N - r - 1) * (N - 1)) := by
    field_simp [hNewNe, hOldNe]
    <;> ring
  have hProduct := mul_le_mul hNewInv hOldInv
    (le_of_lt (one_div_pos.mpr hOldPos))
    (mul_nonneg (by norm_num : (0 : Real) <= 2) hq0)
  have hMultiply := mul_le_mul_of_nonneg_left hProduct hr
  have hRatioEq : r / ((N - r - 1) * (N - 1)) =
      r * (1 / (N - r - 1)) * (1 / (N - 1)) := by
    field_simp [hNewNe, hOldNe]
    <;> ring
  have hRatio0 : 0 <= r / ((N - r - 1) * (N - 1)) :=
    div_nonneg hr (mul_nonneg (le_of_lt hNewPos) (le_of_lt hOldPos))
  refine And.intro hNewPos (And.intro hOldPos
    (And.intro hNewInv (And.intro hOldInv (And.intro hExact ?_))))
  rw [hExact, abs_of_nonneg hRatio0, hRatioEq]
  nlinarith only [hMultiply]

theorem hamiltonian_normalized_correction_difference
    (N r q XNew XOld alpha beta : Real)
    (hN : 4 <= N) (hr : 0 <= r) (hq : N * q = 1) (hSmall : r * q <= 1 / 4)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hDifference : abs (XNew - XOld) <= alpha) (hOld : abs XOld <= beta) :
    abs (XNew / (8 * (N - r - 1)) - XOld / (8 * (N - 1))) <=
      alpha * q / 4 + beta * r * q ^ 2 / 2 := by
  have hShift := hamiltonian_first_correction_rank_shift N r q hN hr hq hSmall
  have hNewPos := hShift.1
  have hOldPos := hShift.2.1
  have hNewInv := hShift.2.2.1
  have hError := hShift.2.2.2.2.2
  have hNewNe : Not (N - r - 1 = 0) := ne_of_gt hNewPos
  have hOldNe : Not (N - 1 = 0) := ne_of_gt hOldPos
  have hExact : XNew / (8 * (N - r - 1)) - XOld / (8 * (N - 1)) =
      (XNew - XOld) * (1 / (N - r - 1)) / 8 +
        XOld * (1 / (N - r - 1) - 1 / (N - 1)) / 8 := by
    field_simp [hNewNe, hOldNe]
    <;> ring
  have hFirst : abs ((XNew - XOld) * (1 / (N - r - 1)) / 8) <= alpha * q / 4 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 8),
      abs_of_pos (one_div_pos.mpr hNewPos)]
    have h := mul_le_mul hDifference hNewInv
      (le_of_lt (one_div_pos.mpr hNewPos)) hAlpha
    nlinarith only [h]
  have hSecond : abs (XOld * (1 / (N - r - 1) - 1 / (N - 1)) / 8) <=
      beta * r * q ^ 2 / 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 8)]
    have h := mul_le_mul hOld hError
      (abs_nonneg (1 / (N - r - 1) - 1 / (N - 1))) hBeta
    nlinarith only [h]
  rw [hExact]
  have hTriangle := abs_add_le ((XNew - XOld) * (1 / (N - r - 1)) / 8)
    (XOld * (1 / (N - r - 1) - 1 / (N - 1)) / 8)
  linarith only [hTriangle, hFirst, hSecond]

end PrimeFactorOscillations
