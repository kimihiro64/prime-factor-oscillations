/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianWeightedWave

/-!
# Signed integration by parts on the actual Gaussian left tail

The rho term and the Gaussian derivative remain coupled until the
exact boundary identity is established. The derivative remainder has
a bound independent of the height of rho. The parameter range used
for integration is Re(rho)>-1, with V>=1.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set Filter

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussian_left_derivative_term_norm_bound
    (V tau u : Real) (rho : Complex) (hV : 1 <= V) :
    norm (Complex.exp (rho * (u : Complex)) *
      (logGaussianWaveSlope V tau u * logGaussianWave V tau u)) <=
      (4 + abs tau) * logGaussianTailScale V * Real.exp ((rho.re + 1) * u) := by
  have hr : (rho * (u : Complex)).re = rho.re * u := by simp [Complex.mul_re]
  rw [norm_mul, Complex.norm_exp, hr]
  calc
    _ <= Real.exp (rho.re * u) *
        ((4 + abs tau) * logGaussianTailScale V * Real.exp u) :=
      mul_le_mul_of_nonneg_left (logGaussianWave_derivative_norm_bound V tau u hV)
        (Real.exp_pos _).le
    _ = _ := by
      rw [show (rho.re + 1) * u = rho.re * u + u by ring, Real.exp_add]
      ring

theorem logGaussian_left_derivative_term_integrable
    (V tau a : Real) (rho : Complex) (hV : 1 <= V) (hRe : -1 < rho.re) :
    IntegrableOn (fun u : Real =>
      Complex.exp (rho * (u : Complex)) *
        (logGaussianWaveSlope V tau u * logGaussianWave V tau u)) (Iic a) := by
  have hc : 0 < rho.re + 1 := by linarith only [hRe]
  have hM := (integrableOn_exp_mul_Iic hc a).const_mul
    ((4 + abs tau) * logGaussianTailScale V)
  have hC : Continuous (fun u : Real => Complex.exp (rho * (u : Complex)) *
      (logGaussianWaveSlope V tau u * logGaussianWave V tau u)) := by
    dsimp only [logGaussianWaveSlope, logGaussianWave, logGaussianDensity]
    fun_prop
  apply hM.mono' hC.aestronglyMeasurable
  exact Eventually.of_forall fun u => logGaussian_left_derivative_term_norm_bound V tau u rho hV

theorem logGaussianWeightedWave_tendsto_atBot
    (V tau : Real) (rho : Complex) (hV : 0 < V) (hRe : -1 < rho.re) :
    Tendsto (logGaussianWeightedWave V tau rho) atBot (nhds 0) := by
  have hc : 0 < rho.re + 1 := by linarith only [hRe]
  have hMul : Tendsto (fun u : Real => (rho.re + 1) * u) atBot atBot := by
    apply Filter.tendsto_atBot.2
    intro b
    filter_upwards [Filter.eventually_le_atBot (b / (rho.re + 1))] with u hu
    calc
      (rho.re + 1) * u <= (rho.re + 1) * (b / (rho.re + 1)) :=
        mul_le_mul_of_nonneg_left hu hc.le
      _ = b := by field_simp [hc.ne']
  have hExp := Real.tendsto_exp_atBot.comp hMul
  have hScale : Tendsto (fun u : Real =>
      logGaussianTailScale V * Real.exp ((rho.re + 1) * u)) atBot (nhds 0) := by
    simpa only [mul_zero, Function.comp_apply] using! hExp.const_mul (logGaussianTailScale V)
  exact squeeze_zero_norm
    (fun u => logGaussianWeightedWave_norm_le_left_exponential V tau u rho hV) hScale

theorem logGaussian_left_integration_by_parts
    (V tau a : Real) (rho : Complex) (hV : 1 <= V) (hRe : -1 < rho.re) :
    rho * integral (volume.restrict (Iic a)) (logGaussianWeightedWave V tau rho) +
      integral (volume.restrict (Iic a)) (fun u : Real =>
        Complex.exp (rho * (u : Complex)) *
          (logGaussianWaveSlope V tau u * logGaussianWave V tau u)) =
      logGaussianWeightedWave V tau rho a := by
  have hVPos : 0 < V := lt_of_lt_of_le Real.zero_lt_one hV
  have hF : IntegrableOn (logGaussianWeightedWave V tau rho) (Iic a) :=
    (logGaussianWeightedWave_integrable V tau rho hVPos).integrableOn
  have hG := logGaussian_left_derivative_term_integrable V tau a rho hV hRe
  have he (u : Real) :
      (rho + logGaussianWaveSlope V tau u) * logGaussianWeightedWave V tau rho u =
        rho * logGaussianWeightedWave V tau rho u +
          Complex.exp (rho * (u : Complex)) *
            (logGaussianWaveSlope V tau u * logGaussianWave V tau u) := by
    dsimp [logGaussianWeightedWave]
    ring
  have hD : IntegrableOn (fun u : Real =>
      (rho + logGaussianWaveSlope V tau u) * logGaussianWeightedWave V tau rho u) (Iic a) := by
    apply ((hF.const_mul rho).add hG).congr
    exact Eventually.of_forall fun u => (he u).symm
  have hFTC := integral_Iic_of_hasDerivAt_of_tendsto'
    (fun u _ => logGaussianWeightedWave_hasDerivAt V tau u rho hVPos) hD
    (logGaussianWeightedWave_tendsto_atBot V tau rho hVPos hRe)
  simp only [sub_zero] at hFTC
  have hEq : (fun u : Real =>
      (rho + logGaussianWaveSlope V tau u) * logGaussianWeightedWave V tau rho u) =
    (fun u : Real => rho * logGaussianWeightedWave V tau rho u +
      Complex.exp (rho * (u : Complex)) *
        (logGaussianWaveSlope V tau u * logGaussianWave V tau u)) := by
    funext u
    exact he u
  rw [hEq, integral_add (hF.const_mul rho) hG, integral_const_mul] at hFTC
  exact hFTC

end PrimeFactorOscillations.PrimeClassDeletion
