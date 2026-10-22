/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPhysicalProbe
import PrimeFactorOscillations.Helpers.LogGaussianPhysicalSpectralTail

/-!
# Exact Gaussian constant and reference-pole cancellation

The cutoff contributions are kept with their signs. The xi constant is
combined with the reference pole before any remainder estimate.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianLeftMoment
    (X V tau : Real) (rho : Complex) : Complex :=
  (X : Complex) ^ rho *
    integral (volume.restrict (Iic (-Real.log X))) (logGaussianWeightedWave V tau rho)

theorem logGaussianSpectralTail_eq_full_moment_sub_left
    (X V tau : Real) (rho : Complex) (hX : 0 < X) (hV : 0 < V) :
    logGaussianSpectralTail X V tau 1 rho =
      (X : Complex) ^ rho *
        Complex.exp ((V : Complex) / 2 * (rho - (tau : Complex) * Complex.I) ^ 2) -
      logGaussianLeftMoment X V tau rho := by
  have hSplit := integral_add_compl (s := Iic (-Real.log X)) measurableSet_Iic
    (logGaussianWeightedWave_integrable V tau rho hV)
  simp only [compl_Iic] at hSplit
  rw [logGaussianWeightedWave_integral V tau rho hV] at hSplit
  have hRight : integral (volume.restrict (Ioi (-Real.log X)))
      (logGaussianWeightedWave V tau rho) =
    Complex.exp ((V : Complex) / 2 * (rho - (tau : Complex) * Complex.I) ^ 2) -
      integral (volume.restrict (Iic (-Real.log X))) (logGaussianWeightedWave V tau rho) :=
    (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hSplit)
  rw [logGaussianSpectralTail_eq_physical_spectral_tail X V tau rho hX, hRight]
  dsimp only [logGaussianLeftMoment]
  ring

theorem logGaussian_constant_pairing
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
      integral volume (logGaussianVerticalKernel X V tau) =
        logGaussianSpectralTail X V tau 1 0 := by
  have h := logGaussianMellinKernel_inverse_tail X V tau 1 (3 / 2)
    hX hV Real.zero_lt_one (by norm_num)
  have hcast : ((3 / 2 : Real) : Complex) = (3 / 2 : Complex) := by norm_num
  simpa only [hcast, Complex.ofReal_one, Complex.one_cpow, one_mul,
    logGaussianVerticalKernel] using! h

theorem logGaussian_reference_pole_pairing
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
      integral volume (fun t : Real => logGaussianVerticalKernel X V tau t /
        ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1)) =
      logGaussianSpectralTail X V tau 1 1 - logGaussianSpectralTail X V tau 1 0 := by
  let H : Real -> Complex := logGaussianVerticalKernel X V tau
  have hcast : ((3 / 2 : Real) : Complex) = (3 / 2 : Complex) := by norm_num
  have hH : Integrable H := by
    simpa only [H, logGaussianVerticalKernel, hcast] using!
      logGaussianMellinKernel_integrable_vertical X V tau (3 / 2) hX hV (by norm_num)
  have hB : Integrable (fun t : Real => H t /
      ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1)) := by
    have h := Robin1984.integrable_vertical_resolvent hH (c := (3 / 2 : Real))
      (rho := (1 : Complex)) (by norm_num)
    simpa only [hcast] using! h
  have hPair := logGaussian_paired_resolvent_integral_eq_tail X V tau (3 / 2) 1
    hX hV (by norm_num) (by norm_num) (by norm_num)
  simp only [hcast, div_one, one_mul] at hPair
  have hFunction : (fun t : Real => logGaussianMellinKernel X V tau
      ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
        (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1) + 1)) =
    (fun t : Real => H t / ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1) + H t) := by
    funext t
    dsimp only [H, logGaussianVerticalKernel]
    ring
  have hInt := integral_add hB hH
  rw [hFunction, hInt, mul_add, logGaussian_constant_pairing X V tau hX hV] at hPair
  exact (eq_sub_iff_add_eq).mpr hPair

theorem logGaussian_centered_reference_identity
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    logGaussianXiConstant * logGaussianSpectralTail X V tau 1 0 +
      (logGaussianSpectralTail X V tau 1 1 - logGaussianSpectralTail X V tau 1 0) -
      (X : Complex) * Complex.exp ((V : Complex) / 2 *
        ((1 : Complex) - (tau : Complex) * Complex.I) ^ 2) =
      -(Real.log (2 * Real.pi) : Complex) *
        Complex.exp ((V : Complex) / 2 * ((0 : Complex) - (tau : Complex) * Complex.I) ^ 2) +
      (Real.log (2 * Real.pi) : Complex) * logGaussianLeftMoment X V tau 0 -
        logGaussianLeftMoment X V tau 1 := by
  have hConst : logGaussianXiConstant - 1 = -(Real.log (2 * Real.pi) : Complex) :=
    Robin1984.robin_weighted_explicit_constant
  rw [logGaussianSpectralTail_eq_full_moment_sub_left X V tau 0 hX hV,
    logGaussianSpectralTail_eq_full_moment_sub_left X V tau 1 hX hV]
  simp only [Complex.cpow_zero, Complex.cpow_one, one_mul]
  have hc : logGaussianXiConstant = 1 - (Real.log (2 * Real.pi) : Complex) := by
    linear_combination hConst
  rw [hc]
  ring

end PrimeFactorOscillations.PrimeClassDeletion
