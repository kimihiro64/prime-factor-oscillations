/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianZetaExplicit

/-!
# The actual positive compensated Gaussian kernel

A unit complex rotation realizes the shifted probe's full norm.
The resulting real kernel lies between zero and twice the density.
Its weighted integral is the actual coupled theta signal.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianPositiveKernel (V tau : Real) (z : Complex) (u : Real) : Real :=
  logGaussianDensity V u *
    (1 + (z * Complex.exp (-(tau : Complex) * Complex.I * (u : Complex))).re)

theorem logGaussianPositiveKernel_bounds
    (V tau u : Real) (z : Complex) (hV : 0 < V) (hz : norm z <= 1) :
    And (0 <= logGaussianPositiveKernel V tau z u)
      (logGaussianPositiveKernel V tau z u <= 2 * logGaussianDensity V u) := by
  have hPhase : norm (Complex.exp (-(tau : Complex) * Complex.I * (u : Complex))) = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  have hNorm : norm (z * Complex.exp (-(tau : Complex) * Complex.I * (u : Complex))) <= 1 := by
    rw [norm_mul, hPhase, mul_one]
    exact hz
  have hReal := abs_le.mp ((Complex.abs_re_le_norm
    (z * Complex.exp (-(tau : Complex) * Complex.I * (u : Complex)))).trans hNorm)
  have hDensity := (logGaussianDensity_pos V u hV).le
  dsimp only [logGaussianPositiveKernel]
  refine And.intro (mul_nonneg hDensity (by linarith only [hReal.1])) ?_
  calc
    _ <= logGaussianDensity V u * 2 :=
      mul_le_mul_of_nonneg_left (by linarith only [hReal.2]) hDensity
    _ = _ := by ring

theorem logGaussianThetaProbe_coupled_positive_integral
    (X V tau : Real) (hX : 1 <= X) (hV : 0 < V) :
    Exists fun z : Complex => And (norm z = 1)
      (And
        (Integrable (fun u : Real =>
          (Chebyshev.theta (X * Real.exp u) - X * Real.exp u) *
            logGaussianPositiveKernel V tau z u))
        ((logGaussianThetaProbe X V 0).re + norm (logGaussianThetaProbe X V tau) =
          integral volume (fun u : Real =>
            (Chebyshev.theta (X * Real.exp u) - X * Real.exp u) *
              logGaussianPositiveKernel V tau z u))) := by
  classical
  let H : Complex := logGaussianThetaProbe X V tau
  have hRotate : Exists fun z : Complex =>
      And (norm z = 1) ((z * H).re = norm H) := by
    by_cases hH : H = 0
    . refine Exists.intro 1 (And.intro (by simp) ?_)
      rw [hH]
      simp
    . let z : Complex := (starRingEnd Complex) H / (norm H : Complex)
      have hNorm : 0 < norm H := norm_pos_iff.mpr hH
      have hCast : Not ((norm H : Complex) = 0) := Complex.ofReal_ne_zero.mpr hNorm.ne'
      have hUnit : norm z = 1 := by
        dsimp only [z]
        rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hNorm]
        field_simp
      have hProduct : z * H = (norm H : Complex) := by
        dsimp only [z]
        rw [div_mul_eq_mul_div, mul_comm ((starRingEnd Complex) H) H,
          Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        field_simp [hCast]
      refine Exists.intro z (And.intro hUnit ?_)
      rw [hProduct, Complex.ofReal_re]
  cases hRotate with
  | intro z hz =>
    let F0 : Real -> Complex := fun u =>
      ((Chebyshev.theta (X * Real.exp u) - X * Real.exp u : Real) : Complex) *
        logGaussianWave V 0 u
    let Ft : Real -> Complex := fun u =>
      ((Chebyshev.theta (X * Real.exp u) - X * Real.exp u : Real) : Complex) *
        logGaussianWave V tau u
    have hF0 : Integrable F0 := logGaussianThetaProbe_integrable X V 0 hX hV
    have hFt : Integrable Ft := logGaussianThetaProbe_integrable X V tau hX hV
    have hI := hF0.add (hFt.const_mul z)
    have hPoint : forall u : Real,
        (F0 u + z * Ft u).re =
          (Chebyshev.theta (X * Real.exp u) - X * Real.exp u) *
            logGaussianPositiveKernel V tau z u := by
      intro u
      dsimp only [F0, Ft, logGaussianPositiveKernel, logGaussianWave]
      simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      ring
    have hRealI : Integrable (fun u : Real =>
        (Chebyshev.theta (X * Real.exp u) - X * Real.exp u) *
          logGaussianPositiveKernel V tau z u) := by
      apply hI.re.congr
      exact Filter.Eventually.of_forall hPoint
    refine Exists.intro z (And.intro hz.1 (And.intro hRealI ?_))
    have hIntegral :
        (integral volume fun u : Real => (F0 u + z * Ft u).re) =
          (integral volume fun u : Real => F0 u + z * Ft u).re :=
      Complex.reCLM.integral_comp_comm hI
    have hIdentity : (integral volume fun u : Real => (F0 u + z * Ft u).re) =
        (logGaussianThetaProbe X V 0).re + (z * H).re := by
      rw [hIntegral, integral_add hF0 (hFt.const_mul z), integral_const_mul]
      rfl
    rw [hz.2] at hIdentity
    calc
      _ = integral volume (fun u : Real => (F0 u + z * Ft u).re) := hIdentity.symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hPoint)

end PrimeFactorOscillations.PrimeClassDeletion
