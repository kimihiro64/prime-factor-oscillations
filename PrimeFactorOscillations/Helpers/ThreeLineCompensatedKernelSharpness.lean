/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CompensatedMomentRoundingSharpness
import PrimeFactorOscillations.Helpers.ThreeLineCompensatedKernel

/-! # Sharpness of the full signed-kernel cubic parity coefficient -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def threeLineOddKernelDefect (n t : Real) : Real :=
  2 * threeLineHorizontalProfile (t * compensatedOddLow n) +
    2 * n * threeLineHorizontalProfile (t * compensatedOddHigh n) -
      ((2 + 2 * n) * threeLineCharge +
        t * (2 * n + 1) * threeLineSizeBiasedProfile t)

def threeLineOddKernelNormalized (n t : Real) : Real :=
  2 * compensatedOddLow n * (compensatedOddLow n - 1) ^ 2 *
      threeLineSizeBiasedRemainder (t * compensatedOddLow n) t +
    2 * n * compensatedOddHigh n * (compensatedOddHigh n - 1) ^ 2 *
      threeLineSizeBiasedRemainder (t * compensatedOddHigh n) t

theorem threeLineOddKernel_scaled_arguments (n t : Real) (hn : 1 <= n)
    (ht : 0 <= t) (htMax : t <= 1 / 16) :
    And (And (0 <= t * compensatedOddLow n) (t * compensatedOddLow n <= 1 / 4))
      (And (0 <= t * compensatedOddHigh n) (t * compensatedOddHigh n <= 1 / 4)) := by
  have hLow := compensatedOddLow_basic_bounds n hn
  have hHigh := compensatedOddHigh_bounds n hn
  have hLowMax := _root_.mul_le_mul_of_nonneg_left (le_of_lt hLow.2) ht
  have hHighMax := _root_.mul_le_mul_of_nonneg_left (le_of_lt hHigh.2) ht
  exact And.intro
    (And.intro (mul_nonneg ht (le_of_lt hLow.1)) (by nlinarith only [hLowMax, htMax]))
    (And.intro (mul_nonneg ht (by linarith)) (by nlinarith only [hHighMax, htMax]))

theorem threeLineKernel_one_cost (t y : Real) (ht : t <= 1 / 4)
    (hMax : t * y <= 1 / 4) :
    threeLineHorizontalProfile (t * y) - threeLineCharge -
      t * y * threeLineSizeBiasedProfile t -
      t ^ 2 * threeLineSizeBiasedSlope t * y * (y - 1) =
      t ^ 3 * y * (y - 1) ^ 2 * threeLineSizeBiasedRemainder (t * y) t := by
  have hPhi := threeLineSizeBiased_identity (t * y) hMax
  have hTangent := congrArg (fun q : Real => t * y * q)
    (threeLineSizeBiased_tangent_identity (t * y) t hMax ht)
  rw [hPhi]
  nlinarith only [hTangent]

theorem threeLineOddKernel_scaled_moments (n t : Real) (hn : 1 <= n) :
    And
      (2 * (t * compensatedOddLow n) + 2 * n * (t * compensatedOddHigh n) = t * (2 * n + 1))
      (2 * (t * compensatedOddLow n) ^ 2 + 2 * n * (t * compensatedOddHigh n) ^ 2 =
        t ^ 2 * (2 * n + 1)) := by
  have hFirst := congrArg (fun q : Real => t * q) (compensatedOdd_first_moment n hn)
  have hSecond := congrArg (fun q : Real => t ^ 2 * q)
    ((compensatedOdd_second_moment n hn).trans (compensatedOdd_first_moment n hn))
  constructor <;> nlinarith only [hFirst, hSecond]

theorem threeLineOddKernel_model_charge (n t : Real) (hn : 1 <= n) (ht : 0 < t) :
    threeLineMomentRatioCharge (2 + 2 * n)
      (2 * (t * compensatedOddLow n) + 2 * n * (t * compensatedOddHigh n))
      (2 * (t * compensatedOddLow n) ^ 2 + 2 * n * (t * compensatedOddHigh n) ^ 2) =
      (2 + 2 * n) * threeLineCharge + t * (2 * n + 1) * threeLineSizeBiasedProfile t := by
  have hMom := threeLineOddKernel_scaled_moments n t hn
  have hCount : 0 < 2 * n + 1 := by linarith
  unfold threeLineMomentRatioCharge
  rw [hMom.1, hMom.2]
  have hRatio : (t ^ 2 * (2 * n + 1)) / (t * (2 * n + 1)) = t := by
    field_simp [ht.ne', hCount.ne']
  rw [hRatio]
  ring

theorem threeLineOddKernel_effective_mass (n t : Real) (hn : 1 <= n) (ht : 0 < t) :
    (2 * (t * compensatedOddLow n) + 2 * n * (t * compensatedOddHigh n)) ^ 2 /
      (2 * (t * compensatedOddLow n) ^ 2 + 2 * n * (t * compensatedOddHigh n) ^ 2) =
      2 * n + 1 := by
  have hMom := threeLineOddKernel_scaled_moments n t hn
  have hCount : 0 < 2 * n + 1 := by linarith
  rw [hMom.1, hMom.2]
  field_simp [ht.ne', hCount.ne']

theorem threeLineOddKernelDefect_factorization (n t : Real) (hn : 1 <= n)
    (ht : 0 <= t) (htMax : t <= 1 / 16) :
    threeLineOddKernelDefect n t = t ^ 3 * threeLineOddKernelNormalized n t := by
  have hArgs := threeLineOddKernel_scaled_arguments n t hn ht htMax
  have hT : t <= 1 / 4 := by linarith
  have hA := congrArg (fun q : Real => 2 * q)
    (threeLineKernel_one_cost t (compensatedOddLow n) hT hArgs.1.2)
  have hB := congrArg (fun q : Real => 2 * n * q)
    (threeLineKernel_one_cost t (compensatedOddHigh n) hT hArgs.2.2)
  have hFirst := congrArg (fun q : Real => t * threeLineSizeBiasedProfile t * q)
    (compensatedOdd_first_moment n hn)
  have hSecond : 2 * compensatedOddLow n * (compensatedOddLow n - 1) +
      2 * n * compensatedOddHigh n * (compensatedOddHigh n - 1) = 0 := by
    have h := compensatedOdd_second_moment n hn
    nlinarith only [h]
  have hCentered := congrArg (fun q : Real => t ^ 2 * threeLineSizeBiasedSlope t * q) hSecond
  unfold threeLineOddKernelDefect threeLineOddKernelNormalized
  nlinarith only [hA, hB, hFirst, hCentered]

theorem threeLineOddKernelNormalized_zero (n : Real) :
    threeLineOddKernelNormalized n 0 =
      threeLineParityCubicCoefficient * compensatedOddEnergy n := by
  unfold threeLineOddKernelNormalized
  simp only [zero_mul, threeLineSizeBiasedRemainder_origin]
  unfold compensatedOddEnergy
  ring

theorem threeLineOddKernelNormalized_continuousAt_zero (n : Real) :
    ContinuousAt (fun t : Real => threeLineOddKernelNormalized n t) 0 := by
  unfold threeLineOddKernelNormalized threeLineSizeBiasedRemainder
  fun_prop (disch := norm_num [threeLineRadius1, threeLineRadius2, threeLineRadius3])

theorem threeLineKernelParity_larger_coefficient_fails (c : Real)
    (hc : momentRoundThreshold * threeLineParityCubicCoefficient < c) :
    exists n : Nat, And (1 <= n)
      (exists t : Real, And (0 < t)
        (And (t <= 1 / 16) (threeLineOddKernelDefect (n : Real) t < c * t ^ 3))) := by
  have hTau := threeLineParityCubicCoefficient_pos
  have hCancel : threeLineParityCubicCoefficient * (c / threeLineParityCubicCoefficient) = c := by
    field_simp [hTau.ne']
  have hScaledTarget : momentRoundThreshold < c / threeLineParityCubicCoefficient := by
    by_contra hNot
    have hLe : c / threeLineParityCubicCoefficient <= momentRoundThreshold := le_of_not_gt hNot
    have hScaled := _root_.mul_le_mul_of_nonneg_left hLe (le_of_lt hTau)
    nlinarith only [hCancel, hScaled, hc]
  choose n hn hEnergy using
    compensatedOddEnergy_sharp (c / threeLineParityCubicCoefficient) hScaledTarget
  have hnReal : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hAtZero : threeLineParityCubicCoefficient * compensatedOddEnergy (n : Real) < c := by
    have hScaled := _root_.mul_lt_mul_of_pos_left hEnergy hTau
    nlinarith only [hScaled, hCancel]
  have hEps : 0 < c - threeLineParityCubicCoefficient * compensatedOddEnergy (n : Real) :=
    sub_pos.mpr hAtZero
  choose radius hRadius hClose using
    (Metric.continuousAt_iff.mp (threeLineOddKernelNormalized_continuousAt_zero (n : Real)))
      (c - threeLineParityCubicCoefficient * compensatedOddEnergy (n : Real)) hEps
  let t : Real := min radius (1 / 16) / 2
  have hMinPos : 0 < min radius (1 / 16) := lt_min hRadius (by norm_num)
  have ht : 0 < t := div_pos hMinPos (by norm_num)
  have hLeft := min_le_left radius (1 / 16 : Real)
  have hRight := min_le_right radius (1 / 16 : Real)
  have hSmall : t < radius := by dsimp only [t]; linarith
  have htMax : t <= 1 / 16 := by dsimp only [t]; linarith
  have hDist : dist t 0 < radius := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    exact hSmall
  have hNear := hClose hDist
  rw [threeLineOddKernelNormalized_zero, Real.dist_eq] at hNear
  have hCost : threeLineOddKernelNormalized (n : Real) t < c := by
    have hUpper := (abs_lt.mp hNear).2
    linarith
  apply Exists.intro n
  apply And.intro hn
  apply Exists.intro t
  apply And.intro ht
  apply And.intro htMax
  rw [threeLineOddKernelDefect_factorization (n : Real) t hnReal (le_of_lt ht) htMax]
  calc
    _ < t ^ 3 * c := _root_.mul_lt_mul_of_pos_left hCost (pow_pos ht 3)
    _ = _ := by ring

end PrimeFactorOscillations
