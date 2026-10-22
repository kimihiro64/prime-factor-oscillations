/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPrimePowerCorrection

/-!
# The uniform logarithmic-scale prime-power bound

For each fixed c>0 one explicit constant controls every real frequency
and every X>=exp(1), with exponent 1/2+c/8 and one logarithm.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussian_prime_power_log_scale_bound
    (X c tau : Real) (hX : 1 <= X) (hLog : 1 <= Real.log X) (hc : 0 < c) :
    norm (logGaussianPsiProbe X (c * Real.log X) tau -
      logGaussianThetaProbe X (c * Real.log X) tau) <=
      (2 * (2 + c / 2 + 2 * c / Real.pi)) *
        X ^ (1 / 2 + c / 8) * Real.log X := by
  have hXPos : 0 < X := lt_of_lt_of_le Real.zero_lt_one hX
  have hLogPos : 0 < Real.log X := lt_of_lt_of_le Real.zero_lt_one hLog
  have hV : 0 < c * Real.log X := mul_pos hc hLogPos
  let r : Real := Real.sqrt (2 * (c * Real.log X) / Real.pi)
  have hr : 0 <= r := Real.sqrt_nonneg _
  have hrSq : r ^ (2 : Nat) = 2 * (c * Real.log X) / Real.pi :=
    Real.sq_sqrt (by positivity)
  have hRoot : r <= 1 + 2 * (c * Real.log X) / Real.pi := by
    nlinarith only [sq_nonneg (r - 1 / 2), hrSq]
  have hAllowance : Real.log X + (c * Real.log X) / 2 + r <=
      (2 + c / 2 + 2 * c / Real.pi) * Real.log X := by
    have hOne : 1 + 2 * (c * Real.log X) / Real.pi <=
        Real.log X + 2 * (c * Real.log X) / Real.pi :=
      add_le_add hLog (le_refl _)
    calc
      _ <= Real.log X + (c * Real.log X) / 2 +
          (Real.log X + 2 * (c * Real.log X) / Real.pi) :=
        add_le_add (le_refl _) (hRoot.trans hOne)
      _ = _ := by ring
  have hPower : Real.sqrt X * Real.exp ((c * Real.log X) / 8) =
      X ^ (1 / 2 + c / 8) := by
    rw [Real.sqrt_eq_rpow]
    simp only [Real.rpow_def_of_pos hXPos]
    rw [<- Real.exp_add]
    congr 1
    ring
  calc
    _ <= 2 * Real.sqrt X * Real.exp ((c * Real.log X) / 8) *
        (Real.log X + (c * Real.log X) / 2 + r) :=
      logGaussian_prime_power_correction_bound X (c * Real.log X) tau hX hV
    _ <= 2 * Real.sqrt X * Real.exp ((c * Real.log X) / 8) *
        ((2 + c / 2 + 2 * c / Real.pi) * Real.log X) :=
      mul_le_mul_of_nonneg_left hAllowance (by positivity)
    _ = _ := by
      rw [show 2 * Real.sqrt X * Real.exp ((c * Real.log X) / 8) =
        2 * (Real.sqrt X * Real.exp ((c * Real.log X) / 8)) by ring, hPower]
      ring

theorem logGaussian_prime_power_uniform_log_scale
    (c : Real) (hc : 0 < c) :
    Exists fun C : Real => And (0 < C) (forall tau X : Real, Real.exp 1 <= X ->
      norm (logGaussianPsiProbe X (c * Real.log X) tau -
        logGaussianThetaProbe X (c * Real.log X) tau) <=
        C * X ^ (1 / 2 + c / 8) * Real.log X) := by
  refine Exists.intro (2 * (2 + c / 2 + 2 * c / Real.pi)) (And.intro (by positivity) ?_)
  intro tau X hX
  have hExp : (1 : Real) <= Real.exp 1 := by
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr (by norm_num : (0 : Real) <= 1))
  have hLog : (1 : Real) <= Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using h
  exact logGaussian_prime_power_log_scale_bound X c tau (hExp.trans hX) hLog hc

end PrimeFactorOscillations.PrimeClassDeletion
