/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasOscillation
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.IteratedRemainder
import PrimeFactorOscillations.Mathlib.NumberTheory.Chebyshev.UnitIntegral

/-!
# Discrete peaks of the canonical Nicolas tail

Exact unit-interval identities transfer real excursions to integer endpoints.
At a local maximum of the tail minus a reciprocal amplitude, the actual theta
error is positive and logarithmically bounded, making its nonlinear log-log
remainder negligible on the reciprocal scale. Analytic excursion supply is a
separate input and is not asserted by this module.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open MeasureTheory Set Robin1984

theorem nicolasK_sub_eq_intervalIntegral {a b : Real} (ha : 2 <= a) (hab : a <= b) :
    nicolasK a - nicolasK b =
      intervalIntegral (fun t : Real => (Chebyshev.theta t - t) *
        ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) a b volume := by
  unfold nicolasK nicolasThetaError nicolasTailKernel
  exact intervalIntegral.integral_Ioi_sub_Ioi
    (nicolasThetaTail_integrableOn_Ioi_two.mono_set (Ioi_subset_Ioi ha)) hab

/-- Unit-length rounding of the actual Nicolas theta tail needs no PNT estimate. -/
theorem nicolasK_sub_abs_le_of_le_add_one
    {a b : Real} (ha : 2 <= a) (hLog : 1 <= Real.log a)
    (hab : a <= b) (hLength : b <= a + 1) :
    abs (nicolasK a - nicolasK b) <= 2 / a := by
  rw [nicolasK_sub_eq_intervalIntegral ha hab]
  exact Chebyshev.theta_error_short_integral_abs_le a b (by linarith) hLog hab hLength

/-- A reciprocal-scale positive real excursion survives rounding down. -/
theorem nicolasK_nat_gt_div_of_real_scaled_gt
    (n : Nat) (hn : 3 <= n) (x A : Real) (hA : 0 <= A)
    (hLog : 1 <= Real.log (n : Real))
    (hLower : (n : Real) <= x) (hUpper : x <= (n : Real) + 1)
    (hSupply : 2 * A + 5 < x * nicolasK x) :
    A / (n : Real) < nicolasK (n : Real) := by
  have hnThree : (3 : Real) <= (n : Real) := by exact_mod_cast hn
  have hnPos : 0 < (n : Real) := by linarith
  have hxPos : 0 < x := hnPos.trans_le hLower
  have hxDouble : x <= 2 * (n : Real) := by linarith
  have hRound := nicolasK_sub_abs_le_of_le_add_one
    (by linarith : (2 : Real) <= (n : Real)) hLog hLower hUpper
  have hKx : 0 < nicolasK x := by
    by_contra hNot
    have hNonpos := mul_nonpos_of_nonneg_of_nonpos hxPos.le (le_of_not_gt hNot)
    linarith
  have hProduct := mul_le_mul_of_nonneg_right hxDouble hKx.le
  have hError := mul_le_mul_of_nonneg_left (abs_le.mp hRound).1 hnPos.le
  have hTwoCancel : (n : Real) * (-(2 / (n : Real))) = -2 := by
    field_simp [hnPos.ne']
  rw [hTwoCancel] at hError
  by_contra hNot
  have hOpposite := mul_le_mul_of_nonneg_left (le_of_not_gt hNot) hnPos.le
  have hACancel : (n : Real) * (A / (n : Real)) = A := by field_simp [hnPos.ne']
  rw [hACancel] at hOpposite
  nlinarith

/-- A reciprocal-scale negative real excursion survives rounding down. -/
theorem nicolasK_nat_neg_of_real_scaled_lt
    (n : Nat) (hn : 3 <= n) (x : Real)
    (hLog : 1 <= Real.log (n : Real))
    (hLower : (n : Real) <= x) (hUpper : x <= (n : Real) + 1)
    (hSupply : x * nicolasK x < -5) :
    nicolasK (n : Real) < 0 := by
  have hnThree : (3 : Real) <= (n : Real) := by exact_mod_cast hn
  have hnPos : 0 < (n : Real) := by linarith
  have hxPos : 0 < x := hnPos.trans_le hLower
  have hxDouble : x <= 2 * (n : Real) := by linarith
  have hRound := nicolasK_sub_abs_le_of_le_add_one
    (by linarith : (2 : Real) <= (n : Real)) hLog hLower hUpper
  have hKx : nicolasK x < 0 := by
    by_contra hNot
    have hNonneg := mul_nonneg hxPos.le (le_of_not_gt hNot)
    linarith
  have hProduct := mul_le_mul_of_nonpos_right hxDouble hKx.le
  have hError := mul_le_mul_of_nonneg_left (abs_le.mp hRound).2 hnPos.le
  have hTwoCancel : (n : Real) * (2 / (n : Real)) = 2 := by field_simp [hnPos.ne']
  rw [hTwoCancel] at hError
  by_contra hNot
  have hNonneg := mul_nonneg hnPos.le (le_of_not_gt hNot)
  nlinarith

/-- Adjacent inequalities at a positive-amplitude discrete peak force a small,
strictly positive actual theta error. -/
theorem nicolasThetaError_bounds_of_adjacent_peak
    (n : Nat) (hn : 2 <= n) (A : Real) (hA : 0 < A)
    (hLeft : nicolasK (n : Real) - A / (n : Real) <=
      nicolasK ((n : Real) + 1) - A / ((n : Real) + 1))
    (hRight : nicolasK ((n : Real) + 2) - A / ((n : Real) + 2) <=
      nicolasK ((n : Real) + 1) - A / ((n : Real) + 1)) :
    0 < nicolasThetaError ((n : Real) + 1) /\
      nicolasThetaError ((n : Real) + 1) <=
        (2 * A + 1) * Real.log ((n : Real) + 1) := by
  have hnTwo : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hnOne : 1 < (n : Real) := by linarith
  have hnPos : 0 < (n : Real) := by linarith
  have hbPos : 0 < (n : Real) + 1 := by linarith
  have hcPos : 0 < (n : Real) + 2 := by linarith
  have hLeftDiff : A / (n : Real) - A / ((n : Real) + 1) =
      A / (((n : Real) + 1) * (n : Real)) := by
    field_simp [hnPos.ne', hbPos.ne']
    ring
  have hRightDiff : A / ((n : Real) + 1) - A / ((n : Real) + 2) =
      A / (((n : Real) + 1) * ((n : Real) + 2)) := by
    field_simp [hbPos.ne', hcPos.ne']
    ring
  have hLeftIntegral : intervalIntegral (fun t : Real => (Chebyshev.theta t - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
      (n : Real) ((n : Real) + 1) volume <=
      A / (((n : Real) + 1) * (n : Real)) := by
    rw [<- nicolasK_sub_eq_intervalIntegral hnTwo (by linarith)]
    linarith
  have hRightIntegral : 0 < intervalIntegral (fun t : Real => (Chebyshev.theta t - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
      ((n : Real) + 1) (((n : Real) + 1) + 1) volume := by
    rw [<- nicolasK_sub_eq_intervalIntegral (by linarith : (2 : Real) <= (n : Real) + 1)
      (by linarith)]
    have hPositive : 0 < A / (((n : Real) + 1) * ((n : Real) + 2)) := by positivity
    have hEndpoint : (n : Real) + 1 + 1 = (n : Real) + 2 := by ring
    rw [hEndpoint]
    linarith
  have hErrorPos := Chebyshev.theta_error_pos_of_unit_integral_pos
    (n + 1) (by simp only [Nat.cast_add, Nat.cast_one]; linarith)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hRightIntegral)
  have hErrorUpper := Chebyshev.theta_error_succ_le_of_unit_integral_le
    n hnOne A hA.le hLeftIntegral
  simp only [Nat.cast_add, Nat.cast_one] at hErrorPos hErrorUpper
  exact And.intro hErrorPos hErrorUpper

/-- The exact nonlinear Nicolas loss at such a discrete peak is negligible
against the reciprocal amplitude. -/
theorem nicolasRemainder_le_of_adjacent_peak
    (n : Nat) (hn : 2 <= n) (A : Real) (hA : 0 < A)
    (hLeft : nicolasK (n : Real) - A / (n : Real) <=
      nicolasK ((n : Real) + 1) - A / ((n : Real) + 1))
    (hRight : nicolasK ((n : Real) + 2) - A / ((n : Real) + 2) <=
      nicolasK ((n : Real) + 1) - A / ((n : Real) + 1)) :
    nicolasThetaError ((n : Real) + 1) /
        (((n : Real) + 1) * Real.log ((n : Real) + 1)) -
      (Real.log (Real.log (Chebyshev.theta ((n : Real) + 1))) -
        Real.log (Real.log ((n : Real) + 1))) <=
      (2 * A + 1) ^ 2 * (Real.log ((n : Real) + 1) + 1) /
        (2 * ((n : Real) + 1) ^ 2) := by
  have hError := nicolasThetaError_bounds_of_adjacent_peak n hn A hA hLeft hRight
  have hnTwo : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hBound := Real.logLog_remainder_le_of_displacement_le_log
    ((n : Real) + 1) (nicolasThetaError ((n : Real) + 1)) (2 * A + 1)
    (by linarith) hError.1.le (by linarith) hError.2
  have hHeight : (n : Real) + 1 + nicolasThetaError ((n : Real) + 1) =
      Chebyshev.theta ((n : Real) + 1) := by unfold nicolasThetaError; ring
  rw [hHeight] at hBound
  exact hBound

end PrimeFactorOscillations
