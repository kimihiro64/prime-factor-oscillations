/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianFourierInversion
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedMellin

/-!
# Exact Gaussian Perron weights and the full complex resolvent

The absolute resolvent-tail theorem is applied to the actual Gaussian
entire kernel. The result retains every complex rho with Re(rho)<sigma.
At rho=0 it is the cumulative weight for the kernel including 1/s.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianSpectralTail
    (X V tau n : Real) (rho : Complex) : Complex :=
  integral (volume.restrict (Ioi (1 : Real))) fun u : Real =>
    (u : Complex) ^ (rho - 1) *
      ((logGaussianDensity V (Real.log (n * u) - Real.log X) : Complex) *
        Complex.exp (-(tau : Complex) * Complex.I *
          ((Real.log (n * u) - Real.log X : Real) : Complex)))

theorem logGaussianEntireKernel_resolvent_tail
    (X V tau n sigma : Real) (rho : Complex)
    (hX : 0 < X) (hV : 0 < V) (hn : 0 < n) (hRho : rho.re < sigma) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        (integral volume fun t : Real =>
          ((n : Complex) ^ (-((sigma : Complex) + (t : Complex) * Complex.I)) *
            logGaussianEntireKernel X V tau
              ((sigma : Complex) + (t : Complex) * Complex.I)) /
            ((sigma : Complex) + (t : Complex) * Complex.I - rho)) =
      logGaussianSpectralTail X V tau n rho := by
  let H : Real -> Complex := fun t =>
    (n : Complex) ^ (-((sigma : Complex) + (t : Complex) * Complex.I)) *
      logGaussianEntireKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I)
  have hH : Integrable H :=
    logGaussianEntireKernel_vertical_integrable X V tau n sigma hX hV hn
  have hSwap := Robin1984.integral_vertical_resolvent_eq_inverse_tail hH hRho
  change (((1 / (2 * Real.pi) : Real) : Complex)) *
    (integral volume fun t => H t /
      ((sigma : Complex) + (t : Complex) * Complex.I - rho)) = _
  rw [hSwap, <- integral_const_mul]
  unfold logGaussianSpectralTail
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  have huPos : 0 < u := lt_trans Real.zero_lt_one hu
  have hi :
      (integral volume fun t : Real =>
        (u : Complex) ^ (-((sigma : Complex) + (t : Complex) * Complex.I)) * H t) =
      (integral volume fun t : Real =>
        ((n * u : Real) : Complex) ^ (-((sigma : Complex) + (t : Complex) * Complex.I)) *
          logGaussianEntireKernel X V tau
            ((sigma : Complex) + (t : Complex) * Complex.I)) := by
    apply integral_congr_ae
    filter_upwards with t
    dsimp [H]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hn.le huPos.le]
    ring
  rw [hi]
  have hInv := logGaussianEntireKernel_inverse_density X V tau (n * u) sigma
    hX hV (mul_pos hn huPos)
  simpa only [mul_left_comm, mul_assoc, mul_comm] using
    congrArg (fun value : Complex => (u : Complex) ^ (rho - 1) * value) hInv

theorem logGaussianMellinKernel_inverse_tail
    (X V tau n sigma : Real)
    (hX : 0 < X) (hV : 0 < V) (hn : 0 < n) (hSigma : 0 < sigma) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        (integral volume fun t : Real =>
          (n : Complex) ^ (-((sigma : Complex) + (t : Complex) * Complex.I)) *
            logGaussianMellinKernel X V tau
              ((sigma : Complex) + (t : Complex) * Complex.I)) =
      logGaussianSpectralTail X V tau n 0 := by
  have h := logGaussianEntireKernel_resolvent_tail X V tau n sigma 0
    hX hV hn (by simpa using hSigma)
  convert h using 1
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  dsimp [logGaussianMellinKernel, logGaussianEntireKernel]
  simp only [sub_zero]
  ring

end PrimeFactorOscillations.PrimeClassDeletion
