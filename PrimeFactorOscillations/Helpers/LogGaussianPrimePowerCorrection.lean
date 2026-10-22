/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPrimePowerMajorant

/-!
# The full prime-power correction for the actual complex Gaussian probes

The entire psi-theta difference is integrated. The bound is uniform in
the real frequency and retains the exact constant from the paper.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianPrimePowerProbe (X V tau : Real) : Complex :=
  integral volume fun u : Real =>
    ((Chebyshev.psi (X * Real.exp u) - Chebyshev.theta (X * Real.exp u) : Real) : Complex) *
      logGaussianWave V tau u

noncomputable def logGaussianThetaProbe (X V tau : Real) : Complex :=
  integral volume fun u : Real =>
    ((Chebyshev.theta (X * Real.exp u) - X * Real.exp u : Real) : Complex) *
      logGaussianWave V tau u

theorem logGaussianPrimePowerProbe_integrable
    (X V tau : Real) (hX : 1 <= X) (hV : 0 < V) :
    Integrable (fun u : Real =>
      ((Chebyshev.psi (X * Real.exp u) - Chebyshev.theta (X * Real.exp u) : Real) : Complex) *
        logGaussianWave V tau u) := by
  have hArg : Measurable (fun u : Real => X * Real.exp u) :=
    measurable_const.mul Real.continuous_exp.measurable
  have hReal : Measurable (fun u : Real =>
      Chebyshev.psi (X * Real.exp u) - Chebyshev.theta (X * Real.exp u)) :=
    (Chebyshev.psi_mono.measurable.comp hArg).sub (Chebyshev.theta_mono.measurable.comp hArg)
  have hCast : Measurable (fun u : Real =>
      ((Chebyshev.psi (X * Real.exp u) - Chebyshev.theta (X * Real.exp u) : Real) : Complex)) :=
    Complex.continuous_ofReal.measurable.comp hReal
  have hMeas : AEStronglyMeasurable (fun u : Real =>
      ((Chebyshev.psi (X * Real.exp u) - Chebyshev.theta (X * Real.exp u) : Real) : Complex) *
        logGaussianWave V tau u) volume :=
    hCast.aestronglyMeasurable.mul (logGaussianWave_integrable V tau hV).aestronglyMeasurable
  apply (logGaussianPrimePowerMajorant_integrable X V hV).mono' hMeas
  exact Filter.Eventually.of_forall fun u =>
    logGaussian_prime_power_wave_norm_bound X V tau u hX hV

theorem logGaussianPrimePowerProbe_norm_bound
    (X V tau : Real) (hX : 1 <= X) (hV : 0 < V) :
    norm (logGaussianPrimePowerProbe X V tau) <=
      2 * Real.sqrt X * Real.exp (V / 8) *
        (Real.log X + V / 2 + Real.sqrt (2 * V / Real.pi)) := by
  have hQ := logGaussianPrimePowerProbe_integrable X V tau hX hV
  have hMajor := logGaussianPrimePowerMajorant_integrable X V hV
  calc
    _ <= integral volume (fun u : Real =>
        norm (((Chebyshev.psi (X * Real.exp u) - Chebyshev.theta (X * Real.exp u) : Real) : Complex) *
          logGaussianWave V tau u)) := norm_integral_le_integral_norm _
    _ <= integral volume (logGaussianPrimePowerMajorant X V) :=
      integral_mono_ae hQ.norm hMajor (Filter.Eventually.of_forall fun u =>
        logGaussian_prime_power_wave_norm_bound X V tau u hX hV)
    _ <= _ := logGaussianPrimePowerMajorant_integral_bound X V hV

theorem logGaussianThetaProbe_integrable
    (X V tau : Real) (hX : 1 <= X) (hV : 0 < V) :
    Integrable (fun u : Real =>
      ((Chebyshev.theta (X * Real.exp u) - X * Real.exp u : Real) : Complex) *
        logGaussianWave V tau u) := by
  have hXPos : 0 < X := lt_of_lt_of_le Real.zero_lt_one hX
  have hPsi := logGaussianPsiProbe_integrable X V tau hXPos hV
  have hQ := logGaussianPrimePowerProbe_integrable X V tau hX hV
  apply (hPsi.sub hQ).congr
  filter_upwards with u
  dsimp only [Pi.sub_apply]
  push_cast
  ring

theorem logGaussianPsiProbe_sub_theta_eq_primePowerProbe
    (X V tau : Real) (hX : 1 <= X) (hV : 0 < V) :
    logGaussianPsiProbe X V tau - logGaussianThetaProbe X V tau =
      logGaussianPrimePowerProbe X V tau := by
  have hXPos : 0 < X := lt_of_lt_of_le Real.zero_lt_one hX
  have hPsi := logGaussianPsiProbe_integrable X V tau hXPos hV
  have hQ := logGaussianPrimePowerProbe_integrable X V tau hX hV
  have hPoint : (fun u : Real =>
      ((Chebyshev.theta (X * Real.exp u) - X * Real.exp u : Real) : Complex) *
        logGaussianWave V tau u) =
    (fun u : Real =>
      ((Chebyshev.psi (X * Real.exp u) - X * Real.exp u : Real) : Complex) *
        logGaussianWave V tau u -
      ((Chebyshev.psi (X * Real.exp u) - Chebyshev.theta (X * Real.exp u) : Real) : Complex) *
        logGaussianWave V tau u) := by
    funext u
    push_cast
    ring
  rw [logGaussianThetaProbe, hPoint, integral_sub hPsi hQ]
  dsimp only [logGaussianPsiProbe, logGaussianPrimePowerProbe]
  ring

theorem logGaussian_prime_power_correction_bound
    (X V tau : Real) (hX : 1 <= X) (hV : 0 < V) :
    norm (logGaussianPsiProbe X V tau - logGaussianThetaProbe X V tau) <=
      2 * Real.sqrt X * Real.exp (V / 8) *
        (Real.log X + V / 2 + Real.sqrt (2 * V / Real.pi)) := by
  rw [logGaussianPsiProbe_sub_theta_eq_primePowerProbe X V tau hX hV]
  exact logGaussianPrimePowerProbe_norm_bound X V tau hX hV

end PrimeFactorOscillations.PrimeClassDeletion
