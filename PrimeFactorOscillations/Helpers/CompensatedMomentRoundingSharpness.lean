/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CompensatedMomentRounding

/-! # Natural even-weight models for the sharp compensated parity penalty -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

def compensatedOddLow (n : Real) : Real :=
  (2 * n + 1 - Real.sqrt (n * (2 * n + 1))) / (2 * (n + 1))

def compensatedOddHigh (n : Real) : Real :=
  1 + (1 / 2 - compensatedOddLow n) / n

def compensatedOddEnergy (n : Real) : Real :=
  2 * compensatedOddLow n * (compensatedOddLow n - 1) ^ 2 +
    2 * n * compensatedOddHigh n * (compensatedOddHigh n - 1) ^ 2

theorem compensatedOddLow_linear (n : Real) (hn : 1 <= n) :
    2 * (n + 1) * compensatedOddLow n =
      2 * n + 1 - Real.sqrt (n * (2 * n + 1)) := by
  have hNot : Not (n + 1 = 0) := ne_of_gt (by linarith)
  dsimp [compensatedOddLow]
  field_simp [hNot]

theorem compensatedOddLow_polynomial (n : Real) (hn : 1 <= n) :
    n * (2 * compensatedOddLow n - (compensatedOddLow n) ^ 2 - 1 / 2) =
      (1 / 2 - compensatedOddLow n) ^ 2 := by
  have hnPos : 0 < n := by linarith
  have hRad : 0 <= n * (2 * n + 1) := mul_nonneg (le_of_lt hnPos) (by linarith)
  have hRoot := Real.sq_sqrt hRad
  have hLinear := compensatedOddLow_linear n hn
  have hShift : 2 * (n + 1) * compensatedOddLow n - (2 * n + 1) =
      -Real.sqrt (n * (2 * n + 1)) := by linarith
  have hSquare : (2 * (n + 1) * compensatedOddLow n - (2 * n + 1)) ^ 2 =
      n * (2 * n + 1) := by
    rw [hShift, neg_sq]
    exact hRoot
  have hFactor : 4 * (n + 1) *
      ((n + 1) * (compensatedOddLow n) ^ 2 - (2 * n + 1) * compensatedOddLow n +
        (2 * n + 1) / 4) = 0 := by
    calc
      _ = (2 * (n + 1) * compensatedOddLow n - (2 * n + 1)) ^ 2 -
          n * (2 * n + 1) := by ring
      _ = 0 := by rw [hSquare]; ring
  have hNot : Not (4 * (n + 1) = 0) := ne_of_gt (by positivity)
  have hQuadratic := (mul_eq_zero.mp hFactor).resolve_left hNot
  nlinarith only [hQuadratic]

theorem compensatedOddLow_basic_bounds (n : Real) (hn : 1 <= n) :
    And (0 < compensatedOddLow n) (compensatedOddLow n < 1 / 2) := by
  have hnPos : 0 < n := by linarith
  have hRad : 0 <= n * (2 * n + 1) := mul_nonneg (le_of_lt hnPos) (by linarith)
  have hRoot := Real.sq_sqrt hRad
  have hNonneg := Real.sqrt_nonneg (n * (2 * n + 1))
  have hLow : n < Real.sqrt (n * (2 * n + 1)) := by nlinarith
  have hHigh : Real.sqrt (n * (2 * n + 1)) < 2 * n + 1 := by nlinarith
  have hDen : 0 < 2 * (n + 1) := by linarith
  constructor
  case left =>
    exact div_pos (sub_pos.mpr hHigh) hDen
  case right =>
    have hLinear := compensatedOddLow_linear n hn
    by_contra hNot
    have hGe : (1 / 2 : Real) <= compensatedOddLow n := le_of_not_gt hNot
    have hMul := mul_nonneg (le_of_lt hDen) (sub_nonneg.mpr hGe)
    nlinarith only [hLinear, hMul, hLow]

theorem compensatedOddLow_threshold_bounds (n : Real) (hn : 1 <= n) :
    And (momentRoundThreshold <= compensatedOddLow n) (compensatedOddLow n < 1 / 2) := by
  have hnPos : 0 < n := by linarith
  have hBasic := compensatedOddLow_basic_bounds n hn
  have hPolynomial := compensatedOddLow_polynomial n hn
  have hRoot := momentRoundThreshold_equation
  have hThreshold := momentRoundThreshold_bounds
  have hPositive : 0 <=
      2 * compensatedOddLow n - (compensatedOddLow n) ^ 2 - 1 / 2 := by
    by_contra hNot
    have hNegative := mul_neg_of_pos_of_neg hnPos (lt_of_not_ge hNot)
    nlinarith only [hPolynomial, hNegative, sq_nonneg (1 / 2 - compensatedOddLow n)]
  refine And.intro ?_ hBasic.2
  by_contra hNot
  have hStrict : compensatedOddLow n < momentRoundThreshold := lt_of_not_ge hNot
  have hFactor : 0 < (momentRoundThreshold - compensatedOddLow n) *
      (2 - compensatedOddLow n - momentRoundThreshold) :=
    mul_pos (sub_pos.mpr hStrict) (by linarith)
  nlinarith only [hPositive, hRoot, hFactor]

theorem compensatedOddHigh_bounds (n : Real) (hn : 1 <= n) :
    And (1 < compensatedOddHigh n) (compensatedOddHigh n < 3 / 2) := by
  have hnPos : 0 < n := by linarith
  have hLow := compensatedOddLow_basic_bounds n hn
  have hDivPos : 0 < (1 / 2 - compensatedOddLow n) / n :=
    div_pos (by linarith) hnPos
  have hDivUpper : (1 / 2 - compensatedOddLow n) / n < 1 / 2 := by
    have hCancel : n * ((1 / 2 - compensatedOddLow n) / n) =
        1 / 2 - compensatedOddLow n := by field_simp [hnPos.ne']
    by_contra hNot
    have hGe : (1 / 2 : Real) <= (1 / 2 - compensatedOddLow n) / n := le_of_not_gt hNot
    have hMul := mul_nonneg (le_of_lt hnPos) (sub_nonneg.mpr hGe)
    nlinarith only [hCancel, hMul, hLow.1, hn]
  dsimp [compensatedOddHigh]
  constructor <;> linarith

theorem compensatedOdd_first_moment (n : Real) (hn : 1 <= n) :
    2 * compensatedOddLow n + 2 * n * compensatedOddHigh n = 2 * n + 1 := by
  have hnPos : 0 < n := by linarith
  dsimp [compensatedOddHigh]
  field_simp [hnPos.ne'] <;> ring

theorem compensatedOdd_second_moment (n : Real) (hn : 1 <= n) :
    2 * (compensatedOddLow n) ^ 2 + 2 * n * (compensatedOddHigh n) ^ 2 =
      2 * compensatedOddLow n + 2 * n * compensatedOddHigh n := by
  have hnPos : 0 < n := by linarith
  have hPolynomial := compensatedOddLow_polynomial n hn
  have hHigh : n * compensatedOddHigh n = n + 1 / 2 - compensatedOddLow n := by
    dsimp [compensatedOddHigh]
    field_simp [hnPos.ne'] <;> ring
  have hProduct : n * (2 * (compensatedOddLow n) ^ 2 +
      2 * n * (compensatedOddHigh n) ^ 2 -
      2 * compensatedOddLow n - 2 * n * compensatedOddHigh n) = 0 := by
    calc
      _ = 2 * (n * ((compensatedOddLow n) ^ 2 - compensatedOddLow n) +
          (n * compensatedOddHigh n) ^ 2 - n * (n * compensatedOddHigh n)) := by ring
      _ = 0 := by
        rw [hHigh]
        nlinarith only [hPolynomial]
  have hZero := (mul_eq_zero.mp hProduct).resolve_left hnPos.ne'
  linarith only [hZero]


theorem compensatedOddLow_excess (n : Real) (hn : 1 <= n) :
    n * (compensatedOddLow n - momentRoundThreshold) <= 1 / 4 := by
  have hnPos : 0 < n := by linarith
  have hBounds := compensatedOddLow_threshold_bounds n hn
  have hBasic := compensatedOddLow_basic_bounds n hn
  have hThreshold := momentRoundThreshold_bounds
  have hRoot := momentRoundThreshold_equation
  have hPolynomial := compensatedOddLow_polynomial n hn
  have hFactor : 0 <= (compensatedOddLow n - momentRoundThreshold) *
      (1 - compensatedOddLow n - momentRoundThreshold) :=
    mul_nonneg (sub_nonneg.mpr hBounds.1) (by linarith)
  have hBase : compensatedOddLow n - momentRoundThreshold <=
      2 * compensatedOddLow n - (compensatedOddLow n) ^ 2 - 1 / 2 := by
    nlinarith only [hFactor, hRoot]
  have hScaled := _root_.mul_le_mul_of_nonneg_left hBase (le_of_lt hnPos)
  have hSquare : (1 / 2 - compensatedOddLow n) ^ 2 <= 1 / 4 := by
    nlinarith [hBasic.1, hBasic.2]
  nlinarith only [hScaled, hPolynomial, hSquare]

theorem compensatedOddEnergy_expansion (n : Real) (hn : 1 <= n) :
    compensatedOddEnergy n =
      2 * compensatedOddLow n * (compensatedOddLow n - 1) ^ 2 +
      2 * (1 / 2 - compensatedOddLow n) ^ 2 / n +
      2 * (1 / 2 - compensatedOddLow n) ^ 3 / n ^ 2 := by
  have hnPos : 0 < n := by linarith
  dsimp [compensatedOddEnergy, compensatedOddHigh]
  field_simp [hnPos.ne'] <;> ring

theorem compensatedOddEnergy_upper (n : Real) (hn : 1 <= n) :
    compensatedOddEnergy n <= momentRoundThreshold + 1 / n := by
  have hnPos : 0 < n := by linarith
  have hBasic := compensatedOddLow_basic_bounds n hn
  have hBounds := compensatedOddLow_threshold_bounds n hn
  have hThreshold := momentRoundThreshold_bounds
  have hRoot := momentRoundThreshold_equation
  have hExcess := compensatedOddLow_excess n hn
  have hFactor : 0 <= (compensatedOddLow n - momentRoundThreshold) *
      (2 - compensatedOddLow n - momentRoundThreshold) :=
    mul_nonneg (sub_nonneg.mpr hBounds.1) (by linarith)
  have hFirstSquare : 2 * (compensatedOddLow n - 1) ^ 2 <= 1 := by
    nlinarith only [hFactor, hRoot]
  have hFirst := _root_.mul_le_mul_of_nonneg_left hFirstSquare (le_of_lt hBasic.1)
  have hdNonneg : 0 <= 1 / 2 - compensatedOddLow n := by linarith
  have hdUpper : 1 / 2 - compensatedOddLow n <= 1 / 2 := by linarith
  have hSecond : 2 * (1 / 2 - compensatedOddLow n) ^ 2 <= 1 / 2 := by
    nlinarith [hBasic.1, hBasic.2]
  have hThird : 2 * (1 / 2 - compensatedOddLow n) ^ 3 <= 1 / 4 := by
    have hProduct := mul_nonneg hdNonneg
      (show 0 <= 1 / 4 - (1 / 2 - compensatedOddLow n) ^ 2 by nlinarith only [hSecond])
    nlinarith only [hProduct, hdUpper]
  have hFirstScaled := _root_.mul_le_mul_of_nonneg_left hFirst (sq_nonneg n)
  have hExcessScaled := _root_.mul_le_mul_of_nonneg_left hExcess (le_of_lt hnPos)
  have hSecondScaled := _root_.mul_le_mul_of_nonneg_left hSecond (le_of_lt hnPos)
  have hIdentity : n ^ 2 * compensatedOddEnergy n =
      n ^ 2 * (2 * compensatedOddLow n * (compensatedOddLow n - 1) ^ 2) +
      2 * n * (1 / 2 - compensatedOddLow n) ^ 2 +
      2 * (1 / 2 - compensatedOddLow n) ^ 3 := by
    dsimp [compensatedOddEnergy, compensatedOddHigh]
    field_simp [hnPos.ne'] <;> ring
  have hCleared : n ^ 2 * compensatedOddEnergy n <= n ^ 2 * momentRoundThreshold + n := by
    nlinarith only [hIdentity, hFirstScaled, hExcessScaled, hSecondScaled, hThird, hn]
  have hInv : n ^ 2 * (1 / n) = n := by field_simp [hnPos.ne']
  by_contra hNot
  have hStrict : momentRoundThreshold + 1 / n < compensatedOddEnergy n := lt_of_not_ge hNot
  have hProduct : 0 < n ^ 2 * (compensatedOddEnergy n - momentRoundThreshold - 1 / n) :=
    mul_pos (sq_pos_of_pos hnPos) (by linarith)
  nlinarith only [hCleared, hInv, hProduct]

theorem compensatedOdd_effective_mass (n : Real) (hn : 1 <= n) :
    (2 * compensatedOddLow n + 2 * n * compensatedOddHigh n) ^ 2 /
      (2 * (compensatedOddLow n) ^ 2 + 2 * n * (compensatedOddHigh n) ^ 2) =
        2 * n + 1 := by
  rw [compensatedOdd_second_moment n hn, compensatedOdd_first_moment n hn]
  have hNot : Not (2 * n + 1 = 0) := ne_of_gt (by linarith)
  field_simp [hNot]

theorem compensatedOdd_rounding_mass (n : Real) (hn : 1 <= n) :
    2 * momentRoundIndicator momentRoundThreshold (compensatedOddLow n) +
      2 * n * momentRoundIndicator momentRoundThreshold (compensatedOddHigh n) =
        2 + 2 * n := by
  have hLow := (compensatedOddLow_threshold_bounds n hn).1
  have hHigh : momentRoundThreshold <= compensatedOddHigh n := by
    have hH := compensatedOddHigh_bounds n hn
    have hT := momentRoundThreshold_bounds
    linarith
  unfold momentRoundIndicator
  rw [ite_eq_left hLow, ite_eq_left hHigh]
  ring

theorem compensatedOdd_rounding_error (n : Real) (hn : 1 <= n) :
    abs (2 * compensatedOddLow n + 2 * n * compensatedOddHigh n -
      (2 * momentRoundIndicator momentRoundThreshold (compensatedOddLow n) +
        2 * n * momentRoundIndicator momentRoundThreshold (compensatedOddHigh n))) = 1 := by
  rw [compensatedOdd_rounding_mass n hn, compensatedOdd_first_moment n hn]
  have h : 2 * n + 1 - (2 + 2 * n) = (-1 : Real) := by ring
  rw [h]
  norm_num

theorem compensatedOddEnergy_lower (n : Real) (hn : 1 <= n) :
    momentRoundThreshold <= compensatedOddEnergy n := by
  have hnPos : 0 < n := by linarith
  have hLow := compensatedOddLow_basic_bounds n hn
  have hHigh := compensatedOddHigh_bounds n hn
  have hLowCut := (compensatedOddLow_threshold_bounds n hn).1
  have hHighCut : momentRoundThreshold <= compensatedOddHigh n := by
    have hT := momentRoundThreshold_bounds
    linarith
  have hFirst := compensatedOdd_first_moment n hn
  have hSecond := compensatedOdd_second_moment n hn
  have hLeft := _root_.mul_le_mul_of_nonneg_left
    (momentRound_compensated_threshold_bounds (compensatedOddLow n) (le_of_lt hLow.1)).1
    (show (0 : Real) <= 2 by norm_num)
  have hRight := _root_.mul_le_mul_of_nonneg_left
    (momentRound_compensated_threshold_bounds (compensatedOddHigh n)
      (show 0 <= compensatedOddHigh n by linarith)).1
    (show 0 <= 2 * n by positivity)
  unfold momentRoundIndicator at hLeft hRight
  rw [ite_eq_left hLowCut] at hLeft
  rw [ite_eq_left hHighCut] at hRight
  have hCompensated : 2 * (2 * compensatedOddLow n - (compensatedOddLow n) ^ 2 - 1) +
      2 * n * (2 * compensatedOddHigh n - (compensatedOddHigh n) ^ 2 - 1) = -1 := by
    nlinarith only [hFirst, hSecond]
  have hCompScaled := congrArg (fun q : Real => momentRoundThreshold * q) hCompensated
  dsimp [compensatedOddEnergy]
  nlinarith only [hLeft, hRight, hCompScaled]

theorem compensatedOdd_natural_parity (n : Nat) :
    And (Even (2 + 2 * n)) (Odd (2 * n + 1)) := by
  exact And.intro (Exists.intro (n + 1) (by ring)) (Exists.intro n (by ring))

theorem compensatedOddEnergy_sharp (c : Real) (hc : momentRoundThreshold < c) :
    exists n : Nat, And (1 <= n) (compensatedOddEnergy (n : Real) < c) := by
  have hDifference : 0 < c - momentRoundThreshold := by linarith
  have hExists := exists_nat_gt (max (1 : Real) (1 / (c - momentRoundThreshold)))
  let n : Nat := Classical.choose hExists
  have hn := Classical.choose_spec hExists
  have hnOne : (1 : Real) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hnNat : 1 <= n := by exact_mod_cast (le_of_lt hnOne)
  have hnReal : (1 : Real) <= n := le_of_lt hnOne
  have hnPos : (0 : Real) < n := by linarith
  have hInverse : 1 / (c - momentRoundThreshold) < n :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hCancel : (c - momentRoundThreshold) * (1 / (c - momentRoundThreshold)) = 1 := by
    field_simp [hDifference.ne']
  have hScaled := _root_.mul_lt_mul_of_pos_left hInverse hDifference
  have hProduct : 1 < (n : Real) * (c - momentRoundThreshold) := by
    nlinarith only [hScaled, hCancel]
  have hInvCancel : (n : Real) * (1 / (n : Real)) = 1 := by field_simp [hnPos.ne']
  have hInvSmall : 1 / (n : Real) < c - momentRoundThreshold := by
    by_contra hNot
    have hGe : c - momentRoundThreshold <= 1 / (n : Real) := le_of_not_gt hNot
    have hMul := _root_.mul_le_mul_of_nonneg_left hGe (le_of_lt hnPos)
    nlinarith only [hMul, hInvCancel, hProduct]
  exact Exists.intro n (And.intro hnNat
    (lt_of_le_of_lt (compensatedOddEnergy_upper (n : Real) hnReal) (by linarith)))

end PrimeFactorOscillations
