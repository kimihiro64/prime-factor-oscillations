/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPhysicalProbe
import PrimeFactorOscillations.Helpers.LogGaussianZeroPairing

/-!
# The full archimedean series for the physical Gaussian test

The existing unconditional gamma interchange is applied to the actual
Gaussian majorant. Every negative even pole remains in the signed identity.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussian_gamma_atom_pairing
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) (k : Nat) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
      integral volume (fun t : Real => logGaussianVerticalKernel X V tau t *
        (1 / (2 * ((k : Complex) + 1)) -
          1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1)))) =
      logGaussianSpectralTail X V tau 1 (-(2 * ((k : Complex) + 1))) /
        (2 * ((k : Complex) + 1)) := by
  let rho : Complex := -(2 * ((k : Complex) + 1))
  have hRho : Not (rho = 0) := by
    intro h
    have hr := congrArg Complex.re h
    simp [rho] at hr
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have hRe : rho.re < (3 / 2 : Real) := by
    simp [rho]
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have hPair := logGaussian_paired_resolvent_integral_eq_tail X V tau (3 / 2) rho
    hX hV (by norm_num) hRho hRe
  have hcast : ((3 / 2 : Real) : Complex) = (3 / 2 : Complex) := by norm_num
  simp only [hcast] at hPair
  have hFunction : (fun t : Real => logGaussianVerticalKernel X V tau t *
      (1 / (2 * ((k : Complex) + 1)) -
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1)))) =
    (fun t : Real => -(logGaussianMellinKernel X V tau
      ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
        (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - rho) + 1 / rho))) := by
    funext t
    dsimp only [logGaussianVerticalKernel, rho]
    simp only [sub_neg_eq_add, div_neg]
    ring
  rw [hFunction, integral_neg, mul_neg, hPair]
  dsimp only [rho]
  simp only [div_neg, neg_mul, neg_neg, one_div]
  ring

theorem logGaussian_complete_gamma_pairing
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
      integral volume (fun t : Real =>
        logGaussianVerticalKernel X V tau t * logGaussianGammaMultiplier t) =
      tsum (fun k : Nat =>
        logGaussianSpectralTail X V tau 1 (-(2 * ((k : Complex) + 1))) /
          (2 * ((k : Complex) + 1))) := by
  let H : Real -> Complex := logGaussianVerticalKernel X V tau
  let C : Real := logGaussianMajorant X V tau (3 / 2)
  have hcast : ((3 / 2 : Real) : Complex) = (3 / 2 : Complex) := by norm_num
  have hH : Integrable H := by
    simpa only [H, logGaussianVerticalKernel, hcast] using!
      logGaussianMellinKernel_integrable_vertical X V tau (3 / 2) hX hV (by norm_num)
  have hC : 0 <= C := (logGaussianMajorant_pos X V tau (3 / 2) hX hV).le
  have hBound (t : Real) : norm (H t) <= C *
      (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat) := by
    simpa only [H, C, logGaussianVerticalKernel, hcast] using
      logGaussianMellinKernel_inverse_square_bound X V tau (3 / 2) t hX hV (by norm_num)
  have hSwap := Robin1984.integral_tsum_gamma_atoms hH hC hBound
  have hIntegral : integral volume (fun t : Real =>
      H t * logGaussianGammaMultiplier t) =
    tsum (fun k : Nat => integral volume (fun t : Real => H t *
      (1 / (2 * ((k : Complex) + 1)) -
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I + 2 * ((k : Complex) + 1))))) := by
    rw [hSwap]
    apply integral_congr_ae
    filter_upwards with t
    rw [tsum_mul_left, logGaussianGammaMultiplier,
      Robin1984.half_digamma_eq_trivial_zero_series (by simp; norm_num)]
    ring
  change (((1 / (2 * Real.pi) : Real) : Complex)) *
    integral volume (fun t : Real => H t * logGaussianGammaMultiplier t) = _
  rw [hIntegral, <- tsum_mul_left]
  apply tsum_congr
  intro k
  exact logGaussian_gamma_atom_pairing X V tau hX hV k

end PrimeFactorOscillations.PrimeClassDeletion
