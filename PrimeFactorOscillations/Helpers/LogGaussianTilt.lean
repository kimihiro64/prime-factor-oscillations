/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianShiftMoment

/-!
# The exact half-power Gaussian tilt and its full absolute moment

The mass is exp(V/8); the absolute-moment allowance is
exp(V/8)*(V/2+sqrt(2*V/pi)). These are the complete prime-power weights.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianDensity_half_tilt (V u : Real) (hV : 0 < V) :
    Real.exp (u / 2) * logGaussianDensity V u =
      Real.exp (V / 8) * logGaussianDensity V (u - V / 2) := by
  have he : u / 2 + -u ^ 2 / (2 * V) =
      V / 8 + -(u - V / 2) ^ 2 / (2 * V) := by
    field_simp [hV.ne']
    <;> ring
  unfold logGaussianDensity
  rw [<- mul_div_assoc, <- mul_div_assoc, <- Real.exp_add, <- Real.exp_add, he]

theorem logGaussianDensity_half_tilt_integrable (V : Real) (hV : 0 < V) :
    Integrable (fun u : Real => Real.exp (u / 2) * logGaussianDensity V u) := by
  have hShift : Integrable (fun u : Real => logGaussianDensity V (u - V / 2)) := by
    simpa only [sub_eq_add_neg] using!
      (logGaussianDensity_integrable V hV).comp_add_right (-(V / 2))
  apply (hShift.const_mul (Real.exp (V / 8))).congr
  exact Filter.Eventually.of_forall fun u => (logGaussianDensity_half_tilt V u hV).symm

theorem logGaussianDensity_half_tilt_integral (V : Real) (hV : 0 < V) :
    (integral volume fun u : Real => Real.exp (u / 2) * logGaussianDensity V u) =
      Real.exp (V / 8) := by
  have hTranslate :
      (integral volume fun u : Real => logGaussianDensity V (u + -(V / 2))) =
        integral volume (logGaussianDensity V) :=
    integral_add_right_eq_self (logGaussianDensity V) (-(V / 2))
  have hShift : (integral volume fun u : Real => logGaussianDensity V (u - V / 2)) = 1 := by
    simpa only [sub_eq_add_neg, logGaussianDensity_integral V hV] using hTranslate
  simp_rw [logGaussianDensity_half_tilt V _ hV]
  rw [integral_const_mul, hShift, mul_one]

theorem logGaussianDensity_half_abs_tilt (V u : Real) (hV : 0 < V) :
    Real.exp (u / 2) * abs u * logGaussianDensity V u =
      Real.exp (V / 8) * (abs u * logGaussianDensity V (u - V / 2)) := by
  calc
    _ = abs u * (Real.exp (u / 2) * logGaussianDensity V u) := by ring
    _ = _ := by rw [logGaussianDensity_half_tilt V u hV]; ring

theorem logGaussianDensity_half_abs_tilt_integrable (V : Real) (hV : 0 < V) :
    Integrable (fun u : Real => Real.exp (u / 2) * abs u * logGaussianDensity V u) := by
  have hShift := logGaussianDensity_shifted_abs_integrable V (V / 2) hV
  apply (hShift.const_mul (Real.exp (V / 8))).congr
  exact Filter.Eventually.of_forall fun u => (logGaussianDensity_half_abs_tilt V u hV).symm

theorem logGaussianDensity_half_abs_tilt_integral_bound (V : Real) (hV : 0 < V) :
    (integral volume fun u : Real => Real.exp (u / 2) * abs u * logGaussianDensity V u) <=
      Real.exp (V / 8) * (V / 2 + Real.sqrt (2 * V / Real.pi)) := by
  have h := logGaussianDensity_shifted_abs_integral_bound V (V / 2) hV
  rw [abs_of_pos (by positivity : 0 < V / 2)] at h
  simp_rw [logGaussianDensity_half_abs_tilt V _ hV]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

end PrimeFactorOscillations.PrimeClassDeletion
