/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.GaussianScalarMajorant
import PrimeFactorOscillations.Helpers.LogGaussianMoment

/-!
# Uniform majorants for the separated Gaussian left tails

The same exponential scale controls the constant and gamma tails and,
after one integration by parts, the omitted part of each zero term.
These are remainder bounds; the complete principal zero sum is retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianTailScale (V : Real) : Real :=
  Real.exp (V / 2) / Real.sqrt (2 * Real.pi * V)

theorem logGaussianTailScale_pos (V : Real) (hV : 0 < V) :
    0 < logGaussianTailScale V := by
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (by positivity))

theorem logGaussianDensity_left_tilt (V u : Real) (hV : 0 < V) :
    logGaussianDensity V u =
      logGaussianTailScale V * Real.exp u * Real.exp (-((u + V) ^ 2 / (2 * V))) := by
  have he : -u ^ 2 / (2 * V) = V / 2 + u + -((u + V) ^ 2 / (2 * V)) := by
    field_simp [hV.ne'] <;> ring
  simp only [logGaussianDensity, logGaussianTailScale, he, Real.exp_add]
  ring

theorem logGaussianDensity_le_left_exponential (V u : Real) (hV : 0 < V) :
    logGaussianDensity V u <= logGaussianTailScale V * Real.exp u := by
  rw [logGaussianDensity_left_tilt V u hV]
  have he : Real.exp (-((u + V) ^ 2 / (2 * V))) <= 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by positivity)))
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left he
      (mul_nonneg (logGaussianTailScale_pos V hV).le (Real.exp_pos u).le)

theorem logGaussianDensity_derivative_size_bound
    (V tau u : Real) (hV : 1 <= V) :
    (abs u / V + abs tau) * logGaussianDensity V u <=
      (4 + abs tau) * logGaussianTailScale V * Real.exp u := by
  have hVPos : 0 < V := lt_of_lt_of_le Real.zero_lt_one hV
  let w : Real := u + V
  let a : Real := 1 / (2 * V)
  let E : Real := Real.exp (-(a * w ^ 2))
  have ha : 0 < a := one_div_pos.mpr (by positivity)
  have hA : abs u <= abs w + V := by
    have h := norm_sub_le (u + V) V
    have he : (u + V) - V = u := by ring
    simpa only [he, Real.norm_eq_abs, abs_of_pos hVPos, w] using h
  have hLinear := linear_gaussian_le a (V * (1 + abs tau)) w ha (by positivity)
  have hMain : (abs u + V * abs tau) * E <= V * (4 + abs tau) := by
    calc
      _ <= (V * (1 + abs tau) + abs w) * E := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith only [hA]
      _ <= V * (1 + abs tau) + 1 + 1 / a := hLinear
      _ <= V * (4 + abs tau) := by
        have he : 1 / a = 2 * V := by dsimp [a]; field_simp [hVPos.ne']
        rw [he]
        nlinarith only [hV]
  have hDiv := div_le_div_of_nonneg_right hMain hVPos.le
  have hScaled : (abs u / V + abs tau) * E <= 4 + abs tau := by
    convert hDiv using 1 <;> field_simp [hVPos.ne'] <;> ring
  have he : Real.exp (-((u + V) ^ 2 / (2 * V))) = E := by
    dsimp [E, a, w]
    congr 1
    ring
  rw [logGaussianDensity_left_tilt V u hVPos, he]
  have h := mul_le_mul_of_nonneg_left hScaled
    (mul_nonneg (logGaussianTailScale_pos V hVPos).le (Real.exp_pos u).le)
  convert h using 1 <;> ring

end PrimeFactorOscillations.PrimeClassDeletion
