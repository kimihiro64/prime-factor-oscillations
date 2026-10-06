/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LcmFiniteTailAsymptotic
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.ZeroConstantBound

/-!
# An explicit positive margin for the finite modified-LCM tail

Bernoulli bounds the finite geometric loss symbolically. Only a two-term
logarithm estimate uses an explicit finite series. The final beta hypothesis
is discharged for Robin's zero constant by the imported attributed port.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

theorem lcmFiniteTailCoefficient_bernoulli_lower
    (s : Real) (hs : 1 <= s) (m : Nat) :
    1 + 1 / s - (1 / s) / (1 + (m : Real) * (s - 1)) <=
      lcmFiniteTailCoefficient (s ^ 2) m := by
  have hs0 : 0 < s := by linarith
  have hSmall : 0 <= (m : Real) * (s - 1) :=
    mul_nonneg (Nat.cast_nonneg m) (by linarith)
  have hDen : 0 < 1 + (m : Real) * (s - 1) := by linarith
  have hBern := one_add_mul_le_pow (a := s - 1) (by linarith : -2 <= s - 1) m
  rw [show 1 + (s - 1) = s by ring] at hBern
  have hInv := one_div_le_one_div_of_le hDen hBern
  have hTail : (1 / s) ^ (m + 1) <= (1 / s) / (1 + (m : Real) * (s - 1)) := by
    calc
      (1 / s) ^ (m + 1) = (1 / s) * (1 / s ^ m) := by
        simp only [pow_succ, div_pow, one_pow]
        ring
      _ <= (1 / s) * (1 / (1 + (m : Real) * (s - 1))) :=
        mul_le_mul_of_nonneg_left hInv (by positivity)
      _ = _ := by ring
  rw [lcmFiniteTailCoefficient_sq s hs0 m]
  linarith

theorem lcmFiniteTailCoefficient_explicit_gt :
    (2 - 1 / 500 : Real) <
      lcmFiniteTailCoefficient ((1001 / 1000 : Real) ^ 2) 1000000 := by
  have hBound := lcmFiniteTailCoefficient_bernoulli_lower
    (1001 / 1000 : Real) (by norm_num) 1000000
  have hRational : (2 - 1 / 500 : Real) <
      1 + 1 / (1001 / 1000 : Real) -
        (1 / (1001 / 1000 : Real)) /
          (1 + (1000000 : Real) * ((1001 / 1000 : Real) - 1)) := by
    norm_num
  exact hRational.trans_le hBound

theorem lcmFiniteTailCoefficient_explicit_margin
    (beta : Real) (hBeta : beta <= 1 / 20) :
    (7 / 600 : Real) <
      lcmFiniteTailCoefficient ((1001 / 1000 : Real) ^ 2) 1000000 *
        Real.exp (-(2 / 5 : Real)) -
          3 * (Real.sqrt 2 - 1) - (3 / 2 : Real) * beta := by
  have hCoeff := lcmFiniteTailCoefficient_explicit_gt
  generalize hCoeffEq :
    lcmFiniteTailCoefficient ((1001 / 1000 : Real) ^ 2) 1000000 = coeff at *
  have hSeries := Real.sum_range_le_log_div (x := (62 / 313 : Real))
    (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hSeries
  have hLog : (2 / 5 : Real) < Real.log (375 / 251 : Real) := by linarith
  have hExpUpper := Real.exp_lt_exp.mpr hLog
  rw [Real.exp_log (by norm_num : (0 : Real) < 375 / 251)] at hExpUpper
  have hExpPos := Real.exp_pos (-(2 / 5 : Real))
  have hCancel : Real.exp (2 / 5 : Real) * Real.exp (-(2 / 5 : Real)) = 1 := by
    rw [<- Real.exp_add]
    norm_num
  have hExpLower : (251 / 375 : Real) < Real.exp (-(2 / 5 : Real)) := by
    have h := mul_lt_mul_of_pos_right hExpUpper
      (show 0 < (251 / 375 : Real) * Real.exp (-(2 / 5 : Real)) by positivity)
    nlinarith
  have hExpOne : Real.exp (-(2 / 5 : Real)) < 1 := by
    have h := Real.exp_lt_exp.mpr (show -(2 / 5 : Real) < 0 by norm_num)
    simpa only [Real.exp_zero] using h
  have hSqrtSq : (Real.sqrt 2) ^ 2 = (2 : Real) := Real.sq_sqrt (by norm_num)
  have hSqrt : Real.sqrt 2 < (17 / 12 : Real) := by
    nlinarith [Real.sqrt_nonneg 2]
  have hLoss : 3 * (Real.sqrt 2 - 1) + (3 / 2 : Real) * beta < 53 / 40 := by
    linarith
  have hPositive : (502 / 375 - 1 / 500 : Real) <
      coeff * Real.exp (-(2 / 5 : Real)) := by
    have h := mul_lt_mul_of_pos_right hCoeff hExpPos
    nlinarith
  linarith

end PrimeFactorOscillations
