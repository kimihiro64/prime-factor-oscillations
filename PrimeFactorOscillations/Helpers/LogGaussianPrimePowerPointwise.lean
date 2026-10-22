/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPhysicalProbe

/-!
# Pointwise domination of the full prime-power correction

The complete difference psi-theta is bounded for every real logarithmic
input, including inputs below one. The unit complex phase is retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianPrimePowerMajorant (X V u : Real) : Real :=
  2 * Real.sqrt X *
    (Real.log X * (Real.exp (u / 2) * logGaussianDensity V u) +
      Real.exp (u / 2) * abs u * logGaussianDensity V u)

theorem logGaussian_prime_power_pointwise_bound
    (X u : Real) (hX : 1 <= X) :
    abs (Chebyshev.psi (X * Real.exp u) - Chebyshev.theta (X * Real.exp u)) <=
      2 * Real.sqrt X * Real.exp (u / 2) * (Real.log X + abs u) := by
  have hXPos : 0 < X := lt_of_lt_of_le Real.zero_lt_one hX
  have hLogX : 0 <= Real.log X := Real.log_nonneg hX
  have hLog : Real.log (X * Real.exp u) = Real.log X + u := by
    rw [Real.log_mul hXPos.ne' (Real.exp_pos u).ne', Real.log_exp]
  have hExp : Real.exp u = Real.exp (u / 2) ^ (2 : Nat) := by
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  have hSqrt : Real.sqrt (X * Real.exp u) = Real.sqrt X * Real.exp (u / 2) := by
    rw [Real.sqrt_mul hXPos.le, hExp, Real.sqrt_sq (Real.exp_pos _).le]
  by_cases hInput : 1 <= X * Real.exp u
  . calc
      _ <= 2 * Real.sqrt (X * Real.exp u) * Real.log (X * Real.exp u) :=
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hInput
      _ = 2 * Real.sqrt X * Real.exp (u / 2) * (Real.log X + u) := by
        rw [hSqrt, hLog]
        ring
      _ <= _ := mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (Real.log X)) (le_abs_self u)) (by positivity)
  . have hSmall : X * Real.exp u <= 1 := (lt_of_not_ge hInput).le
    rw [Chebyshev.psi_eq_zero_of_le_one hSmall, Chebyshev.theta_eq_zero_of_le_one hSmall]
    simp only [sub_self, abs_zero]
    positivity

theorem logGaussian_prime_power_wave_norm_bound
    (X V tau u : Real) (hX : 1 <= X) (hV : 0 < V) :
    norm (((Chebyshev.psi (X * Real.exp u) - Chebyshev.theta (X * Real.exp u) : Real) : Complex) *
      logGaussianWave V tau u) <= logGaussianPrimePowerMajorant X V u := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, logGaussianWave_norm V tau u hV]
  calc
    _ <= (2 * Real.sqrt X * Real.exp (u / 2) * (Real.log X + abs u)) *
        logGaussianDensity V u :=
      mul_le_mul_of_nonneg_right (logGaussian_prime_power_pointwise_bound X u hX)
        (by unfold logGaussianDensity; positivity)
    _ = _ := by
      dsimp only [logGaussianPrimePowerMajorant]
      ring

end PrimeFactorOscillations.PrimeClassDeletion
