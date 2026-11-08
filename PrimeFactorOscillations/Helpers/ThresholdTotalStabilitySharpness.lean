/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FinCases
import PrimeFactorOscillations.Helpers.ThresholdTotalBoundary

/-! # Fixed even-weight sharpness of the upper-boundary square-root rate -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdUpperSharpRadius (s : Real) : Real := s * Real.sqrt (2 - 4 * s ^ 2)

def thresholdUpperSharpOrder : Fin 3 -> Nat := ![6, 1, 1]

def thresholdUpperSharpCoord (s : Real) : Fin 3 -> Real :=
  ![1 / 2 - s ^ 2, 3 / 2 - s ^ 2 + thresholdUpperSharpRadius s,
    3 / 2 - s ^ 2 - thresholdUpperSharpRadius s]

theorem thresholdUpperSharpRadius_bounds (s : Real) (hs : And (0 < s) (s <= 1 / 4)) :
    And (s <= thresholdUpperSharpRadius s)
      (And (thresholdUpperSharpRadius s <= 1 / 2)
        ((thresholdUpperSharpRadius s) ^ 2 = 2 * s ^ 2 - 4 * s ^ 4)) := by
  have hs2 : s ^ 2 <= 1 / 16 := by nlinarith only [hs.1, hs.2]
  have hArg : 1 <= 2 - 4 * s ^ 2 := by linarith only [hs2]
  have hSqrt := Real.sq_sqrt (show 0 <= 2 - 4 * s ^ 2 by linarith only [hArg])
  have hPos := Real.sqrt_nonneg (2 - 4 * s ^ 2)
  have hOne : 1 <= Real.sqrt (2 - 4 * s ^ 2) := by nlinarith only [hSqrt, hPos, hArg]
  have hTwo : Real.sqrt (2 - 4 * s ^ 2) <= 2 := by
    nlinarith only [hSqrt, hPos, sq_nonneg s]
  have hLower : s <= thresholdUpperSharpRadius s := by
    dsimp [thresholdUpperSharpRadius]
    nlinarith only [mul_le_mul_of_nonneg_left hOne hs.1.le]
  have hUpper : thresholdUpperSharpRadius s <= 1 / 2 := by
    dsimp [thresholdUpperSharpRadius]
    nlinarith only [mul_le_mul_of_nonneg_left hTwo hs.1.le, hs.2]
  refine And.intro hLower (And.intro hUpper ?_)
  dsimp [thresholdUpperSharpRadius]
  calc
    _ = s ^ 2 * (Real.sqrt (2 - 4 * s ^ 2)) ^ 2 := by ring
    _ = _ := by rw [hSqrt]; ring

theorem thresholdUpperSharp_profile (s : Real) (hs : And (0 < s) (s <= 1 / 4)) :
    And (forall i : Fin 3, 0 <= thresholdUpperSharpCoord s i)
      (And (Finset.sum Finset.univ (fun i : Fin 3 => 2 * (thresholdUpperSharpOrder i : Real)) = 16)
        (And (thresholdSelectedMass (1 / 2) Finset.univ
          (fun i : Fin 3 => 2 * (thresholdUpperSharpOrder i : Real))
          (thresholdUpperSharpCoord s) = 4)
          (And (Finset.sum Finset.univ (fun i : Fin 3 =>
            2 * (thresholdUpperSharpOrder i : Real) * thresholdUpperSharpCoord s i) =
              12 - 16 * s ^ 2)
            (Finset.sum Finset.univ (fun i : Fin 3 =>
              2 * (thresholdUpperSharpOrder i : Real) * (thresholdUpperSharpCoord s i) ^ 2) =
                12 - 16 * s ^ 2)))) := by
  have hr := thresholdUpperSharpRadius_bounds s hs
  have hs2 : s ^ 2 <= 1 / 16 := by nlinarith only [hs.1, hs.2]
  have hlo : 1 / 2 - s ^ 2 < (1 / 2 : Real) := by nlinarith only [sq_pos_of_pos hs.1]
  have hp : (1 / 2 : Real) <= 3 / 2 - s ^ 2 + thresholdUpperSharpRadius s := by
    linarith only [hs2, hr.1, hs.1]
  have hm : (1 / 2 : Real) <= 3 / 2 - s ^ 2 - thresholdUpperSharpRadius s := by
    linarith only [hs2, hr.2.1]
  refine And.intro ?hCoords (And.intro ?hTotal (And.intro ?hSelected (And.intro ?hFirst ?hSecond)))
  case hCoords =>
    intro i
    fin_cases i <;> norm_num [thresholdUpperSharpCoord]
    all_goals linarith only [hs2, hp, hm]
  case hTotal => norm_num [thresholdUpperSharpOrder, Fin.sum_univ_succ]
  case hSelected =>
    norm_num [thresholdSelectedMass, thresholdUpperSharpOrder, thresholdUpperSharpCoord,
      Fin.sum_univ_succ, momentRoundIndicator, not_le.mpr hlo, hp, hm]
  case hFirst =>
    norm_num [thresholdUpperSharpOrder, thresholdUpperSharpCoord, Fin.sum_univ_succ]
    ring
  case hSecond =>
    norm_num [thresholdUpperSharpOrder, thresholdUpperSharpCoord, Fin.sum_univ_succ]
    nlinarith only [hr.2.2]

theorem thresholdUpperSharp_statistic (s : Real) (hs : And (0 < s) (s <= 1 / 4)) :
    4 * s <= Finset.sum Finset.univ (fun i : Fin 3 =>
      2 * (thresholdUpperSharpOrder i : Real) *
        abs (thresholdUpperSharpCoord s i - 3 / 2)) - 12 := by
  have hr := thresholdUpperSharpRadius_bounds s hs
  have hs2 : s ^ 2 <= s := by nlinarith only [hs.1, hs.2]
  have hZero : abs (thresholdUpperSharpCoord s 0 - 3 / 2) = 1 + s ^ 2 := by
    change abs (1 / 2 - s ^ 2 - 3 / 2) = _
    rw [abs_of_nonpos (by nlinarith only [sq_nonneg s])]
    ring
  have hOne : abs (thresholdUpperSharpCoord s 1 - 3 / 2) =
      thresholdUpperSharpRadius s - s ^ 2 := by
    change abs (3 / 2 - s ^ 2 + thresholdUpperSharpRadius s - 3 / 2) = _
    rw [abs_of_nonneg (by linarith only [hr.1, hs2])]
    ring
  have hTwo : abs (thresholdUpperSharpCoord s 2 - 3 / 2) =
      thresholdUpperSharpRadius s + s ^ 2 := by
    change abs (3 / 2 - s ^ 2 - thresholdUpperSharpRadius s - 3 / 2) = _
    rw [abs_of_nonpos (by nlinarith only [hr.1, hs.1, sq_nonneg s])]
    ring
  have hSum : Finset.sum Finset.univ (fun i : Fin 3 =>
      2 * (thresholdUpperSharpOrder i : Real) * abs (thresholdUpperSharpCoord s i - 3 / 2)) =
      12 * abs (thresholdUpperSharpCoord s 0 - 3 / 2) +
        2 * abs (thresholdUpperSharpCoord s 1 - 3 / 2) +
        2 * abs (thresholdUpperSharpCoord s 2 - 3 / 2) := by
    norm_num [thresholdUpperSharpOrder, Fin.sum_univ_succ]
    ring
  rw [hSum, hZero, hOne, hTwo]
  nlinarith only [hr.1, sq_nonneg s]

theorem thresholdUpperSharp_small_gap (epsilon : Real) (he : 0 < epsilon) :
    exists s : Real, And (And (0 < s) (s <= 1 / 4))
      (And (0 < 16 * s ^ 2) (16 * s ^ 2 < epsilon)) := by
  let s := min (1 / 4 : Real) (epsilon / 32)
  have hs : 0 < s := lt_min (by norm_num) (div_pos he (by norm_num))
  have hSmall : s <= 1 / 4 := min_le_left _ _
  have heSmall : s <= epsilon / 32 := min_le_right _ _
  have hGap : 16 * s ^ 2 < epsilon := by
    have hProd := mul_nonneg hs.le (sub_nonneg.mpr hSmall)
    nlinarith only [hProd, heSmall, he]
  exact Exists.intro s (And.intro (And.intro hs hSmall)
    (And.intro (mul_pos (by norm_num) (sq_pos_of_pos hs)) hGap))

theorem thresholdUpperSharp_boundary :
    And (thresholdModelHigh 12 4 (1 / 2) = 3 / 2)
      (thresholdTotalUpper (1 / 2) 16 4 = 12) := by
  have hSq := Real.sq_sqrt (show (0 : Real) <= 4 by norm_num)
  have hRoot : Real.sqrt (4 : Real) = 2 := by
    nlinarith only [hSq, Real.sqrt_nonneg (4 : Real)]
  norm_num [thresholdTotalUpper, thresholdModelHigh]
  norm_num [hRoot]

theorem thresholdUpperSharp_test_lipschitz :
    forall u v : Real,
      abs (abs (u - 3 / 2) - abs (v - 3 / 2)) <= abs (u - v) := by
  intro u v
  calc
    _ <= abs ((u - 3 / 2) - (v - 3 / 2)) := abs_abs_sub_abs_le_abs_sub _ _
    _ = _ := by congr 1; ring
theorem thresholdUpperSharp_arbitrarily_small (epsilon : Real) (he : 0 < epsilon) :
    exists s : Real, And (And (0 < s) (s <= 1 / 4))
      (And (0 < 16 * s ^ 2) (And (16 * s ^ 2 < epsilon)
        (Real.sqrt (16 * s ^ 2) <= Finset.sum Finset.univ (fun i : Fin 3 =>
          2 * (thresholdUpperSharpOrder i : Real) *
            abs (thresholdUpperSharpCoord s i - 3 / 2)) - 12))) := by
  choose s hs hPos hSmall using thresholdUpperSharp_small_gap epsilon he
  have hSq := Real.sq_sqrt hPos.le
  have hRoot : Real.sqrt (16 * s ^ 2) = 4 * s := by
    nlinarith only [hSq, Real.sqrt_nonneg (16 * s ^ 2), hs.1]
  refine Exists.intro s (And.intro hs (And.intro hPos (And.intro hSmall ?_)))
  rw [hRoot]
  exact thresholdUpperSharp_statistic s hs

end PrimeFactorOscillations
