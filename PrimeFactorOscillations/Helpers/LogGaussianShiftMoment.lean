/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianAbsoluteMoment

/-!
# Normalization and exact shifted absolute-moment bound

The same normalized density is retained under real translations.
The absolute-moment allowance is abs(a)+sqrt(2*V/pi).
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianDensity_integrable (V : Real) (hV : 0 < V) :
    Integrable (logGaussianDensity V) := by
  have h := (logGaussianDensity_integrable_complex_moment V hV 0).re
  simpa only [zero_mul, Complex.exp_zero, mul_one, Complex.ofReal_re] using! h

theorem logGaussianDensity_integral (V : Real) (hV : 0 < V) :
    integral volume (logGaussianDensity V) = 1 := by
  have hRoot : Not (Real.sqrt (2 * Real.pi * V) = 0) :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  have hFunction : (fun u : Real => Real.exp (-u ^ 2 / (2 * V))) =
      (fun u : Real => Real.exp (-(1 / (2 * V)) * u ^ 2)) := by
    funext u
    congr 1
    ring
  have hArg : Real.pi / (1 / (2 * V)) = 2 * Real.pi * V := by
    field_simp [hV.ne']
  change (integral volume fun u : Real =>
    Real.exp (-u ^ 2 / (2 * V)) / Real.sqrt (2 * Real.pi * V)) = 1
  have hFactor : (fun u : Real =>
      Real.exp (-u ^ 2 / (2 * V)) / Real.sqrt (2 * Real.pi * V)) =
    (fun u : Real => Real.exp (-u ^ 2 / (2 * V)) *
      Inv.inv (Real.sqrt (2 * Real.pi * V))) := by
    funext u
    exact div_eq_mul_inv _ _
  rw [hFactor, integral_mul_const, hFunction, integral_gaussian, hArg]
  field_simp [hRoot]

theorem logGaussianDensity_centered_abs_shift_integrable
    (V a : Real) (hV : 0 < V) :
    Integrable (fun u : Real => abs (u + a) * logGaussianDensity V u) := by
  have hI := (logGaussianDensity_first_moment_integrable V hV).add
    ((logGaussianDensity_integrable V hV).const_mul a)
  apply hI.norm.congr
  filter_upwards with u
  change norm (u * logGaussianDensity V u + a * logGaussianDensity V u) =
    abs (u + a) * logGaussianDensity V u
  rw [<- add_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (logGaussianDensity_pos V u hV)]

theorem logGaussianDensity_shifted_abs_integrable
    (V a : Real) (hV : 0 < V) :
    Integrable (fun u : Real => abs u * logGaussianDensity V (u - a)) := by
  have h := (logGaussianDensity_centered_abs_shift_integrable V a hV).comp_add_right (-a)
  simpa only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero] using! h

theorem logGaussianDensity_shifted_abs_integral_bound
    (V a : Real) (hV : 0 < V) :
    (integral volume fun u : Real => abs u * logGaussianDensity V (u - a)) <=
      abs a + Real.sqrt (2 * V / Real.pi) := by
  let F : Real -> Real := fun u => abs u * logGaussianDensity V (u - a)
  have hTranslate : integral volume (fun u : Real => F (u + a)) = integral volume F :=
    integral_add_right_eq_self F a
  have hShift : (integral volume fun u : Real => abs u * logGaussianDensity V (u - a)) =
      integral volume (fun u : Real => abs (u + a) * logGaussianDensity V u) := by
    simpa only [F, add_sub_cancel_right] using hTranslate.symm
  have hAbs := logGaussianDensity_abs_moment_integrable V hV
  have hConst := (logGaussianDensity_integrable V hV).const_mul (abs a)
  rw [hShift]
  calc
    _ <= integral volume (fun u : Real =>
        abs u * logGaussianDensity V u + abs a * logGaussianDensity V u) := by
      apply integral_mono_ae (logGaussianDensity_centered_abs_shift_integrable V a hV)
        (hAbs.add hConst)
      filter_upwards with u
      dsimp only [Pi.add_apply]
      have hAdd : abs (u + a) <= abs u + abs a := by
        simpa only [Real.norm_eq_abs] using norm_add_le u a
      calc
        _ <= (abs u + abs a) * logGaussianDensity V u :=
          mul_le_mul_of_nonneg_right hAdd (logGaussianDensity_pos V u hV).le
        _ = _ := by ring
    _ = _ := by
      rw [integral_add hAbs hConst, integral_const_mul,
        logGaussianDensity_abs_moment V hV, logGaussianDensity_integral V hV]
      ring

end PrimeFactorOscillations.PrimeClassDeletion
