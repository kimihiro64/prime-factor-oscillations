/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianReferenceResidues

/-!
# Explicit left-tail bounds for the constant and reference pole

The bound applies uniformly to the actual physical Gaussian moment.
At rho=0 and rho=1 it gives the two cutoff errors in the full formula.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussian_left_weighted_integral_norm_bound
    (V tau a : Real) (rho : Complex) (hV : 0 < V) (hRe : -1 < rho.re) :
    norm (integral (volume.restrict (Iic a)) (logGaussianWeightedWave V tau rho)) <=
      logGaussianTailScale V * Real.exp ((rho.re + 1) * a) / (rho.re + 1) := by
  have hc : 0 < rho.re + 1 := by linarith only [hRe]
  have hF := (logGaussianWeightedWave_integrable V tau rho hV).integrableOn (s := Iic a)
  have hM := (integrableOn_exp_mul_Iic hc a).const_mul (logGaussianTailScale V)
  calc
    _ <= integral (volume.restrict (Iic a)) (fun u : Real =>
        norm (logGaussianWeightedWave V tau rho u)) := norm_integral_le_integral_norm _
    _ <= integral (volume.restrict (Iic a)) (fun u : Real =>
        logGaussianTailScale V * Real.exp ((rho.re + 1) * u)) := by
      apply integral_mono_ae hF.norm hM
      exact Filter.Eventually.of_forall fun u =>
        logGaussianWeightedWave_norm_le_left_exponential V tau u rho hV
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Iic hc a]
      ring

theorem logGaussianLeftMoment_norm_bound
    (X V tau : Real) (rho : Complex) (hX : 0 < X) (hV : 0 < V)
    (hRe : -1 < rho.re) :
    norm (logGaussianLeftMoment X V tau rho) <=
      logGaussianTailScale V / (X * (rho.re + 1)) := by
  let c : Real := rho.re + 1
  let a : Real := -Real.log X
  have hPower : X ^ rho.re * Real.exp (c * a) = 1 / X := by
    rw [Real.rpow_def_of_pos hX, <- Real.exp_add]
    have he : Real.log X * rho.re + c * a = -Real.log X := by dsimp [c, a]; ring
    rw [he, Real.exp_neg, Real.exp_log hX, one_div]
  rw [logGaussianLeftMoment, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
  calc
    _ <= X ^ rho.re *
        (logGaussianTailScale V * Real.exp (c * a) / c) :=
      mul_le_mul_of_nonneg_left
        (logGaussian_left_weighted_integral_norm_bound V tau a rho hV hRe)
        (Real.rpow_nonneg hX.le _)
    _ = logGaussianTailScale V * (X ^ rho.re * Real.exp (c * a)) / c := by ring
    _ = logGaussianTailScale V / (X * (rho.re + 1)) := by
      rw [hPower]
      dsimp only [c]
      have hc : Not (rho.re + 1 = 0) := by linarith only [hRe]
      field_simp [hX.ne', hc]

end PrimeFactorOscillations.PrimeClassDeletion
