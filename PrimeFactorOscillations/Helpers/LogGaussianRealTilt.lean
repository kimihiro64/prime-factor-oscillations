/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianShiftMoment

/-!
# General real Gaussian tilting for the physical localization tail

The shift is V*t and the mass is exp(V*t^2/2). The existing exact
shifted absolute moment controls the complete first-moment allowance.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianDensity_real_tilt (V t u : Real) (hV : 0 < V) :
    Real.exp (t * u) * logGaussianDensity V u =
      Real.exp (V * t ^ 2 / 2) * logGaussianDensity V (u - V * t) := by
  have he : t * u + -u ^ 2 / (2 * V) =
      V * t ^ 2 / 2 + -(u - V * t) ^ 2 / (2 * V) := by
    field_simp [hV.ne']
    <;> ring
  unfold logGaussianDensity
  rw [<- mul_div_assoc, <- mul_div_assoc, <- Real.exp_add, <- Real.exp_add, he]

theorem logGaussianDensity_real_tilt_integrable (V t : Real) (hV : 0 < V) :
    Integrable (fun u : Real => Real.exp (t * u) * logGaussianDensity V u) := by
  have hShift : Integrable (fun u : Real => logGaussianDensity V (u - V * t)) := by
    simpa only [sub_eq_add_neg] using!
      (logGaussianDensity_integrable V hV).comp_add_right (-(V * t))
  apply (hShift.const_mul (Real.exp (V * t ^ 2 / 2))).congr
  exact Filter.Eventually.of_forall fun u => (logGaussianDensity_real_tilt V t u hV).symm

theorem logGaussianDensity_real_tilt_integral (V t : Real) (hV : 0 < V) :
    (integral volume fun u : Real => Real.exp (t * u) * logGaussianDensity V u) =
      Real.exp (V * t ^ 2 / 2) := by
  have hTranslate :
      (integral volume fun u : Real => logGaussianDensity V (u + -(V * t))) =
        integral volume (logGaussianDensity V) :=
    integral_add_right_eq_self (logGaussianDensity V) (-(V * t))
  have hShift : (integral volume fun u : Real => logGaussianDensity V (u - V * t)) = 1 := by
    simpa only [sub_eq_add_neg, logGaussianDensity_integral V hV] using hTranslate
  simp_rw [logGaussianDensity_real_tilt V t _ hV]
  rw [integral_const_mul, hShift, mul_one]

theorem logGaussianDensity_real_abs_tilt_integrable (V t : Real) (hV : 0 < V) :
    Integrable (fun u : Real =>
      Real.exp (t * u) * abs u * logGaussianDensity V u) := by
  have hShift := logGaussianDensity_shifted_abs_integrable V (V * t) hV
  apply (hShift.const_mul (Real.exp (V * t ^ 2 / 2))).congr
  filter_upwards with u
  change Real.exp (V * t ^ 2 / 2) *
    (abs u * logGaussianDensity V (u - V * t)) =
      Real.exp (t * u) * abs u * logGaussianDensity V u
  rw [show Real.exp (t * u) * abs u * logGaussianDensity V u =
    abs u * (Real.exp (t * u) * logGaussianDensity V u) by ring,
    logGaussianDensity_real_tilt V t u hV]
  ring

theorem logGaussianDensity_real_abs_tilt_integral_bound (V t : Real) (hV : 0 < V) :
    (integral volume fun u : Real =>
      Real.exp (t * u) * abs u * logGaussianDensity V u) <=
        Real.exp (V * t ^ 2 / 2) *
          (abs (V * t) + Real.sqrt (2 * V / Real.pi)) := by
  have hPoint : (fun u : Real =>
      Real.exp (t * u) * abs u * logGaussianDensity V u) =
    (fun u : Real => Real.exp (V * t ^ 2 / 2) *
      (abs u * logGaussianDensity V (u - V * t))) := by
    funext u
    rw [show Real.exp (t * u) * abs u * logGaussianDensity V u =
      abs u * (Real.exp (t * u) * logGaussianDensity V u) by ring,
      logGaussianDensity_real_tilt V t u hV]
    ring
  rw [hPoint, integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (logGaussianDensity_shifted_abs_integral_bound V (V * t) hV)
    (Real.exp_pos _).le

end PrimeFactorOscillations.PrimeClassDeletion
