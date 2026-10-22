/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianWaveDerivative

/-!
# The actual exponential Gaussian wave for each complex zero

The pointwise estimates apply for every complex rho. Positivity of
Re(rho)+1 is used only later when integrating the separated left tail.
The original complex phase is retained in the actual functions.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianWeightedWave (V tau : Real) (rho : Complex) (u : Real) : Complex :=
  Complex.exp (rho * (u : Complex)) * logGaussianWave V tau u

theorem logGaussianWeightedWave_integrable
    (V tau : Real) (rho : Complex) (hV : 0 < V) :
    Integrable (logGaussianWeightedWave V tau rho) := by
  have he (u : Real) :
      logGaussianWeightedWave V tau rho u =
        (logGaussianDensity V u : Complex) *
          Complex.exp ((rho - (tau : Complex) * Complex.I) * (u : Complex)) := by
    dsimp only [logGaussianWeightedWave, logGaussianWave]
    rw [show (rho - (tau : Complex) * Complex.I) * (u : Complex) =
      rho * (u : Complex) + (-(tau : Complex) * Complex.I * (u : Complex)) by ring,
      Complex.exp_add]
    ring
  apply (logGaussianDensity_integrable_complex_moment V hV
    (rho - (tau : Complex) * Complex.I)).congr
  exact Filter.Eventually.of_forall fun u => (he u).symm

theorem logGaussianWeightedWave_hasDerivAt
    (V tau u : Real) (rho : Complex) (hV : 0 < V) :
    HasDerivAt (logGaussianWeightedWave V tau rho)
      ((rho + logGaussianWaveSlope V tau u) * logGaussianWeightedWave V tau rho u) u := by
  have hReal : HasDerivAt (fun v : Real => (v : Complex)) 1 u := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := u))
  have hExp := (HasDerivAt.const_mul rho hReal).cexp
  have hWave := logGaussianWave_hasDerivAt V tau u hV
  have hProduct := hExp.mul hWave
  convert hProduct using 1
  . rfl
  . dsimp only [logGaussianWeightedWave]
    ring

theorem logGaussianWeightedWave_norm_le_left_exponential
    (V tau u : Real) (rho : Complex) (hV : 0 < V) :
    norm (logGaussianWeightedWave V tau rho u) <=
      logGaussianTailScale V * Real.exp ((rho.re + 1) * u) := by
  have hr : (rho * (u : Complex)).re = rho.re * u := by simp [Complex.mul_re]
  rw [logGaussianWeightedWave, norm_mul, Complex.norm_exp, hr, logGaussianWave_norm V tau u hV]
  calc
    _ <= Real.exp (rho.re * u) * (logGaussianTailScale V * Real.exp u) :=
      mul_le_mul_of_nonneg_left (logGaussianDensity_le_left_exponential V u hV)
        (Real.exp_pos _).le
    _ = _ := by
      rw [show (rho.re + 1) * u = rho.re * u + u by ring, Real.exp_add]
      ring

theorem logGaussianWeightedWave_derivative_norm_le_left_exponential
    (V tau u : Real) (rho : Complex) (hV : 1 <= V) :
    norm ((rho + logGaussianWaveSlope V tau u) * logGaussianWeightedWave V tau rho u) <=
      (norm rho + 4 + abs tau) * logGaussianTailScale V *
        Real.exp ((rho.re + 1) * u) := by
  have hVPos : 0 < V := lt_of_lt_of_le Real.zero_lt_one hV
  have hr : (rho * (u : Complex)).re = rho.re * u := by simp [Complex.mul_re]
  have he :
      (rho + logGaussianWaveSlope V tau u) * logGaussianWeightedWave V tau rho u =
        Complex.exp (rho * (u : Complex)) *
          (rho * logGaussianWave V tau u +
            logGaussianWaveSlope V tau u * logGaussianWave V tau u) := by
    dsimp [logGaussianWeightedWave]
    ring
  rw [he, norm_mul, Complex.norm_exp, hr]
  calc
    _ <= Real.exp (rho.re * u) *
        (norm (rho * logGaussianWave V tau u) +
          norm (logGaussianWaveSlope V tau u * logGaussianWave V tau u)) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
    _ <= Real.exp (rho.re * u) *
        (norm rho * (logGaussianTailScale V * Real.exp u) +
          (4 + abs tau) * logGaussianTailScale V * Real.exp u) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply add_le_add
      . rw [norm_mul, logGaussianWave_norm V tau u hVPos]
        exact mul_le_mul_of_nonneg_left (logGaussianDensity_le_left_exponential V u hVPos)
          (norm_nonneg rho)
      . exact logGaussianWave_derivative_norm_bound V tau u hV
    _ = _ := by
      rw [show (rho.re + 1) * u = rho.re * u + u by ring, Real.exp_add]
      ring

end PrimeFactorOscillations.PrimeClassDeletion
