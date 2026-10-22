/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianMajorant
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedStripExplicit
import PrimeFactorOscillations.Helpers.XiZeroStrip

/-!
# Unconditional full xi-series interchange for the actual Gaussian test

Every canonical divisor-zero index is retained, including multiplicity.
The upper-strip assumption of the existing interchange theorem is proved
for those actual zeros. No RH or extra zero-location premise is supplied.
This establishes convergence and interchange, not the physical Perron
identity or the left-contour error in the paper's explicit formula.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open MeasureTheory

theorem logGaussian_xi_atoms_summable_norm (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      integral volume (fun t : Real => norm (
        logGaussianMellinKernel X V tau ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
          (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p)))) := by
  let H : Real -> Complex := fun t =>
    logGaussianMellinKernel X V tau ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let C : Real := logGaussianMajorant X V tau (3 / 2)
  have hcast : ((3 / 2 : Real) : Complex) = (3 / 2 : Complex) := by norm_num
  have hH : Integrable H := by
    simpa only [H, hcast] using
      logGaussianMellinKernel_integrable_vertical X V tau (3 / 2) hX hV (by norm_num)
  have hC : 0 <= C := (logGaussianMajorant_pos X V tau (3 / 2) hX hV).le
  have hBound (t : Real) : norm (H t) <= C *
      (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat) := by
    simpa only [H, C, hcast] using
      logGaussianMellinKernel_inverse_square_bound X V tau (3 / 2) t hX hV (by norm_num)
  exact Robin1984.summable_integral_norm_paired_xi_atoms_strip (H := H) (C := C)
    (fun p => (xiDivisorZeroValue_re_bounds p).2.le) hH hC hBound

theorem logGaussian_xi_integral_tsum (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    tsum (fun p : RiemannXiDivisorZeroIndex => integral volume (fun t : Real =>
      logGaussianMellinKernel X V tau ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
        (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p))) =
    integral volume (fun t : Real => tsum (fun p : RiemannXiDivisorZeroIndex =>
      logGaussianMellinKernel X V tau ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
        (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p))) := by
  let H : Real -> Complex := fun t =>
    logGaussianMellinKernel X V tau ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let C : Real := logGaussianMajorant X V tau (3 / 2)
  have hcast : ((3 / 2 : Real) : Complex) = (3 / 2 : Complex) := by norm_num
  have hH : Integrable H := by
    simpa only [H, hcast] using
      logGaussianMellinKernel_integrable_vertical X V tau (3 / 2) hX hV (by norm_num)
  have hC : 0 <= C := (logGaussianMajorant_pos X V tau (3 / 2) hX hV).le
  have hBound (t : Real) : norm (H t) <= C *
      (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat) := by
    simpa only [H, C, hcast] using
      logGaussianMellinKernel_inverse_square_bound X V tau (3 / 2) t hX hV (by norm_num)
  exact Robin1984.integral_tsum_paired_xi_atoms_strip (H := H) (C := C)
    (fun p => (xiDivisorZeroValue_re_bounds p).2.le) hH hC hBound

theorem logGaussian_xi_series_integrable (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    Integrable (fun t : Real =>
      logGaussianMellinKernel X V tau ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p)) := by
  let H : Real -> Complex := fun t =>
    logGaussianMellinKernel X V tau ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let C : Real := logGaussianMajorant X V tau (3 / 2)
  have hcast : ((3 / 2 : Real) : Complex) = (3 / 2 : Complex) := by norm_num
  have hH : Integrable H := by
    simpa only [H, hcast] using
      logGaussianMellinKernel_integrable_vertical X V tau (3 / 2) hX hV (by norm_num)
  have hC : 0 <= C := (logGaussianMajorant_pos X V tau (3 / 2) hX hV).le
  have hBound (t : Real) : norm (H t) <= C *
      (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat) := by
    simpa only [H, C, hcast] using
      logGaussianMellinKernel_inverse_square_bound X V tau (3 / 2) t hX hV (by norm_num)
  exact Robin1984.integrable_complete_xi_test_strip (H := H) (C := C)
    (fun p => (xiDivisorZeroValue_re_bounds p).2.le) hH hC hBound

end PrimeFactorOscillations.PrimeClassDeletion
