/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThreeLineCompensatedKernelSharpness

/-! # Exact optimality of the fixed-scale compensated parity coefficient -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def threeLineKernelModelExtension (t : Real) (p : Prod Real Real) : Real :=
  2 * p.1 * (p.1 - 1) ^ 2 * threeLineSizeBiasedRemainder (t * p.1) t +
    (2 * (1 + (1 / 2 - p.1) * p.2) * (1 / 2 - p.1) ^ 2 * p.2) *
      threeLineSizeBiasedRemainder (t * (1 + (1 / 2 - p.1) * p.2)) t

theorem threeLineOddKernel_extended_arguments (n t : Real) (hn : 1 <= n)
    (ht : 0 <= t) (htMax : t <= 9 / 64) :
    And (And (0 <= t * compensatedOddLow n) (t * compensatedOddLow n <= 1 / 4))
      (And (0 <= t * compensatedOddHigh n) (t * compensatedOddHigh n <= 1 / 4)) := by
  have hLow := compensatedOddLow_basic_bounds n hn
  have hHigh := compensatedOddHigh_bounds n hn
  constructor
  case left =>
    constructor
    case left => exact mul_nonneg ht (le_of_lt hLow.1)
    case right => nlinarith
  case right =>
    constructor
    case left => exact mul_nonneg ht (by linarith)
    case right => nlinarith

theorem threeLineOddKernelDefect_extended_factorization (n t : Real) (hn : 1 <= n)
    (ht : 0 <= t) (htMax : t <= 9 / 64) :
    threeLineOddKernelDefect n t = t ^ 3 * threeLineOddKernelNormalized n t := by
  have hArgs := threeLineOddKernel_extended_arguments n t hn ht htMax
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

theorem threeLineKernelModelExtension_model (n t : Real) (hn : 1 <= n) :
    threeLineKernelModelExtension t (compensatedOddLow n, 1 / n) =
      threeLineOddKernelNormalized n t := by
  have hnNot : Not (n = 0) := ne_of_gt (by linarith)
  have hHigh : 1 + (1 / 2 - compensatedOddLow n) * (1 / n) =
      compensatedOddHigh n := by
    unfold compensatedOddHigh
    ring
  have hCoef : 2 * compensatedOddHigh n * (1 / 2 - compensatedOddLow n) ^ 2 * (1 / n) =
      2 * n * compensatedOddHigh n * (compensatedOddHigh n - 1) ^ 2 := by
    unfold compensatedOddHigh
    field_simp [hnNot]
    ring
  unfold threeLineKernelModelExtension threeLineOddKernelNormalized
  dsimp only
  rw [hHigh, hCoef]

theorem threeLineKernelModelExtension_origin (t : Real) :
    threeLineKernelModelExtension t (momentRoundThreshold, 0) =
      threeLineKernelParityCoefficient t := by
  have hRoot := momentRoundThreshold_equation
  have hCoef : 2 * momentRoundThreshold * (momentRoundThreshold - 1) ^ 2 =
      momentRoundThreshold := by nlinarith only [hRoot]
  unfold threeLineKernelModelExtension threeLineKernelParityCoefficient
  simp only [mul_zero, add_zero, zero_mul]
  rw [hCoef]

theorem threeLineKernelModelExtension_continuousAt (t : Real)
    (ht : 0 <= t) (htMax : t <= 9 / 64) :
    ContinuousAt (threeLineKernelModelExtension t) (momentRoundThreshold, 0) := by
  have hD := momentRoundThreshold_bounds
  have hArg : t * momentRoundThreshold <= 1 / 4 := by nlinarith
  have hLow := threeLineMomentRatio_denominators_pos (t * momentRoundThreshold) hArg
  have hHigh := threeLineMomentRatio_denominators_pos t (by linarith)
  have hLow1 := hLow.1
  have hLow2 := hLow.2.1
  have hLow3 := hLow.2.2
  have hHigh1 := hHigh.1
  have hHigh2 := hHigh.2.1
  have hHigh3 := hHigh.2.2
  have hr1 : 0 < threeLineRadius1 := by norm_num [threeLineRadius1]
  have hr2 : 0 < threeLineRadius2 := by norm_num [threeLineRadius2]
  have hr3 : 0 < threeLineRadius3 := by norm_num [threeLineRadius3]
  unfold threeLineKernelModelExtension threeLineSizeBiasedRemainder
  fun_prop (disch := norm_num only [mul_zero, add_zero, mul_one]; positivity)

theorem compensatedOdd_parameters_close (n r : Real) (hn : 1 <= n)
    (_hr : 0 < r) (hnr : 1 < n * r) :
    dist (compensatedOddLow n, 1 / n) (momentRoundThreshold, 0) < r := by
  have hLow := compensatedOddLow_threshold_bounds n hn
  have hExcess := compensatedOddLow_excess n hn
  have hnPos : 0 < n := by linarith
  have hInvPos : 0 < 1 / n := div_pos (by norm_num) hnPos
  have hInv : (1 / n) * n = 1 := by field_simp [hnPos.ne']
  have hA : compensatedOddLow n - momentRoundThreshold < r := by
    by_contra hNot
    have hLe := le_of_not_gt hNot
    have hMul := _root_.mul_le_mul_of_nonneg_left hLe (le_of_lt hnPos)
    nlinarith only [hExcess, hMul, hnr]
  have hB : 1 / n < r := by
    by_contra hNot
    have hLe := le_of_not_gt hNot
    have hMul := _root_.mul_le_mul_of_nonneg_right hLe (le_of_lt hnPos)
    nlinarith only [hInv, hMul, hnr]
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero,
    abs_of_nonneg (sub_nonneg.mpr hLow.1), abs_of_pos hInvPos]
  exact max_lt hA hB

theorem threeLineOddKernel_fixed_scale_limit (t : Real)
    (ht : 0 < t) (htMax : t <= 9 / 64) (eps : Real) (hEps : 0 < eps) :
    exists N : Nat, And (1 <= N) (forall n : Nat, N <= n ->
      abs (threeLineOddKernelNormalized (n : Real) t -
        threeLineKernelParityCoefficient t) < eps) := by
  have hLocal : exists r : Real, And (0 < r) (forall p : Prod Real Real,
      dist p (momentRoundThreshold, 0) < r ->
        dist (threeLineKernelModelExtension t p)
          (threeLineKernelModelExtension t (momentRoundThreshold, 0)) < eps) := by
    exact (Metric.continuousAt_iff.mp
      (threeLineKernelModelExtension_continuousAt t (le_of_lt ht) htMax)) eps hEps
  choose r hr hClose using hLocal
  choose N hN using exists_nat_gt (max 1 (1 / r))
  have hN1 : (1 : Real) < (N : Real) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNr : 1 / r < (N : Real) := lt_of_le_of_lt (le_max_right _ _) hN
  have hCancel : (1 / r) * r = 1 := by field_simp [hr.ne']
  have hNrMul := _root_.mul_lt_mul_of_pos_right hNr hr
  apply Exists.intro N
  apply And.intro (by exact_mod_cast (show (1 : Real) <= (N : Real) by linarith))
  intro n hn
  have hnReal : (N : Real) <= (n : Real) := by exact_mod_cast hn
  have hn1 : (1 : Real) <= (n : Real) := by linarith
  have hnr : 1 < (n : Real) * r := by nlinarith
  have hNear := hClose (compensatedOddLow (n : Real), 1 / (n : Real))
    (compensatedOdd_parameters_close (n : Real) r hn1 hr hnr)
  rw [threeLineKernelModelExtension_model (n : Real) t hn1,
    threeLineKernelModelExtension_origin, Real.dist_eq] at hNear
  exact hNear

theorem threeLineOddKernel_fixed_scale_lower (n t : Real)
    (hn : 1 <= n) (ht : 0 < t) (htMax : t <= 9 / 64) :
    threeLineKernelParityCoefficient t <= threeLineOddKernelNormalized n t := by
  have hLow := compensatedOddLow_threshold_bounds n hn
  have hHigh := compensatedOddHigh_bounds n hn
  have hD := momentRoundThreshold_bounds
  have hArgs := threeLineOddKernel_extended_arguments n t hn (le_of_lt ht) htMax
  have hA := (threeLineKernel_compensated_bounds t (compensatedOddLow n)
    ht htMax (by linarith) hArgs.1.2).1
  have hB := (threeLineKernel_compensated_bounds t (compensatedOddHigh n)
    ht htMax (by linarith) hArgs.2.2).1
  have hRoundA : momentRoundIndicator momentRoundThreshold (compensatedOddLow n) = 1 := by
    unfold momentRoundIndicator
    exact ite_eq_left hLow.1
  have hRoundB : momentRoundIndicator momentRoundThreshold (compensatedOddHigh n) = 1 := by
    unfold momentRoundIndicator
    exact ite_eq_left (by linarith)
  rw [hRoundA] at hA
  rw [hRoundB] at hB
  have hAA := _root_.mul_le_mul_of_nonneg_left hA (show (0 : Real) <= 2 by norm_num)
  have hBB := _root_.mul_le_mul_of_nonneg_left hB (show 0 <= 2 * n by linarith)
  have hFirst := compensatedOdd_first_moment n hn
  have hSecond := compensatedOdd_second_moment n hn
  have hIdentity :
      2 * (threeLineKernelParityCoefficient t *
        (2 * compensatedOddLow n - compensatedOddLow n ^ 2 - 1)) +
      2 * n * (threeLineKernelParityCoefficient t *
        (2 * compensatedOddHigh n - compensatedOddHigh n ^ 2 - 1)) =
      -threeLineKernelParityCoefficient t := by
    calc
      _ = threeLineKernelParityCoefficient t *
          (2 * (2 * compensatedOddLow n + 2 * n * compensatedOddHigh n) -
            (2 * compensatedOddLow n ^ 2 + 2 * n * compensatedOddHigh n ^ 2) -
            (2 + 2 * n)) := by ring
      _ = _ := by rw [hSecond, hFirst]; ring
  unfold threeLineOddKernelNormalized
  nlinarith only [hAA, hBB, hIdentity]

theorem threeLineKernelParity_fixed_scale_sharp (t c : Real)
    (ht : 0 < t) (htMax : t <= 9 / 64)
    (hc : threeLineKernelParityCoefficient t < c) :
    exists n : Nat, And (1 <= n) (threeLineOddKernelNormalized (n : Real) t < c) := by
  choose N hN hClose using
    threeLineOddKernel_fixed_scale_limit t ht htMax
      (c - threeLineKernelParityCoefficient t) (sub_pos.mpr hc)
  apply Exists.intro N
  apply And.intro hN
  have hNear := hClose N (le_refl N)
  have hUpper := (abs_lt.mp hNear).2
  linarith

theorem threeLineKernelParity_fixed_scale_defect_sharp (t c : Real)
    (ht : 0 < t) (htMax : t <= 9 / 64)
    (hc : threeLineKernelParityCoefficient t < c) :
    exists n : Nat, And (1 <= n) (threeLineOddKernelDefect (n : Real) t < c * t ^ 3) := by
  choose n hn hCost using threeLineKernelParity_fixed_scale_sharp t c ht htMax hc
  have hnReal : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  apply Exists.intro n
  apply And.intro hn
  rw [threeLineOddKernelDefect_extended_factorization (n : Real) t hnReal (le_of_lt ht) htMax]
  calc
    _ < t ^ 3 * c := _root_.mul_lt_mul_of_pos_left hCost (pow_pos ht 3)
    _ = _ := by ring

theorem threeLineKernelParity_fixed_scale_optimal_iff (t c : Real)
    (ht : 0 < t) (htMax : t <= 9 / 64) :
    (forall n : Nat, 1 <= n -> c * t ^ 3 <= threeLineOddKernelDefect (n : Real) t) <->
      c <= threeLineKernelParityCoefficient t := by
  constructor
  case mp =>
    intro hAll
    by_contra hNot
    have hc := lt_of_not_ge hNot
    choose n hn hBad using threeLineKernelParity_fixed_scale_defect_sharp t c ht htMax hc
    exact (not_lt_of_ge (hAll n hn)) hBad
  case mpr =>
    intro hc n hn
    have hnReal : (1 : Real) <= (n : Real) := by exact_mod_cast hn
    have hLower := le_trans hc (threeLineOddKernel_fixed_scale_lower (n : Real) t hnReal ht htMax)
    have hScaled := _root_.mul_le_mul_of_nonneg_right hLower (le_of_lt (pow_pos ht 3))
    rw [threeLineOddKernelDefect_extended_factorization (n : Real) t hnReal (le_of_lt ht) htMax]
    nlinarith only [hScaled]

theorem threeLineOddKernel_high_exceeds_scale (n t : Real)
    (hn : 1 <= n) (ht : 0 < t) :
    t < t * compensatedOddHigh n := by
  have hHigh := (compensatedOddHigh_bounds n hn).1
  nlinarith only [hHigh, ht]

end PrimeFactorOscillations
