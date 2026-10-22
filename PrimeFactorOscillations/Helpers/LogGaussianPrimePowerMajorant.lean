/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPrimePowerPointwise
import PrimeFactorOscillations.Helpers.LogGaussianTilt

/-!
# Integration of the complete prime-power Gaussian allowance

The integral keeps the exact mass exp(V/8) and the absolute first
moment sqrt(2*V/pi). Norm domination is used only on X>=1.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianPrimePowerMajorant_integrable
    (X V : Real) (hV : 0 < V) :
    Integrable (logGaussianPrimePowerMajorant X V) := by
  have h := (((logGaussianDensity_half_tilt_integrable V hV).const_mul (Real.log X)).add
    (logGaussianDensity_half_abs_tilt_integrable V hV)).const_mul (2 * Real.sqrt X)
  simpa only [logGaussianPrimePowerMajorant] using! h

theorem logGaussianPrimePowerMajorant_integral_bound
    (X V : Real) (hV : 0 < V) :
    integral volume (logGaussianPrimePowerMajorant X V) <=
      2 * Real.sqrt X * Real.exp (V / 8) *
        (Real.log X + V / 2 + Real.sqrt (2 * V / Real.pi)) := by
  have hF := (logGaussianDensity_half_tilt_integrable V hV).const_mul (Real.log X)
  have hG := logGaussianDensity_half_abs_tilt_integrable V hV
  change (integral volume fun u : Real => 2 * Real.sqrt X *
    (Real.log X * (Real.exp (u / 2) * logGaussianDensity V u) +
      Real.exp (u / 2) * abs u * logGaussianDensity V u)) <= _
  rw [integral_const_mul, integral_add hF hG, integral_const_mul,
    logGaussianDensity_half_tilt_integral V hV]
  calc
    _ <= 2 * Real.sqrt X * (Real.log X * Real.exp (V / 8) +
        Real.exp (V / 8) * (V / 2 + Real.sqrt (2 * V / Real.pi))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (Real.log X * Real.exp (V / 8)))
          (logGaussianDensity_half_abs_tilt_integral_bound V hV))
        (by positivity)
    _ = _ := by ring

end PrimeFactorOscillations.PrimeClassDeletion
