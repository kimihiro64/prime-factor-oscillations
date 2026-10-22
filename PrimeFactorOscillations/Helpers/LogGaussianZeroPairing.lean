/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPerronWeight
import PrimeFactorOscillations.Helpers.LogGaussianXiInterchange

/-!
# Physical pairing of the complete regularized xi atom

The reciprocal s cancels algebraically against the complete paired
resolvent, leaving the nonzero factor 1/rho. Every canonical xi index
and its multiplicity are retained. No zero-location premise beyond
the already proved actual critical-strip bound is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussian_paired_resolvent_integral_eq_tail
    (X V tau sigma : Real) (rho : Complex)
    (hX : 0 < X) (hV : 0 < V) (hSigma : 0 < sigma)
    (hRho : Not (rho = 0)) (hRe : rho.re < sigma) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        (integral volume fun t : Real =>
          logGaussianMellinKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I) *
            (1 / ((sigma : Complex) + (t : Complex) * Complex.I - rho) + 1 / rho)) =
      (1 / rho) * logGaussianSpectralTail X V tau 1 rho := by
  have hTail := logGaussianEntireKernel_resolvent_tail X V tau 1 sigma rho
    hX hV Real.zero_lt_one hRe
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at hTail
  have hPoint (t : Real) :
      logGaussianMellinKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I) *
          (1 / ((sigma : Complex) + (t : Complex) * Complex.I - rho) + 1 / rho) =
        (1 / rho) * (logGaussianEntireKernel X V tau
          ((sigma : Complex) + (t : Complex) * Complex.I) /
            ((sigma : Complex) + (t : Complex) * Complex.I - rho)) := by
    let s : Complex := (sigma : Complex) + (t : Complex) * Complex.I
    have hsRe : s.re = sigma := by simp [s]
    have hs : Not (s = 0) := by
      intro h
      have hr := congrArg Complex.re h
      rw [hsRe, Complex.zero_re] at hr
      linarith only [hr, hSigma]
    have hDiff : Not (s - rho = 0) := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.sub_re, hsRe, Complex.zero_re] at hr
      linarith only [hr, hRe]
    change logGaussianMellinKernel X V tau s * (1 / (s - rho) + 1 / rho) =
      (1 / rho) * (logGaussianEntireKernel X V tau s / (s - rho))
    dsimp only [logGaussianMellinKernel, logGaussianEntireKernel]
    field_simp [hs, hRho, hDiff] <;> ring
  calc
    _ = (((1 / (2 * Real.pi) : Real) : Complex)) *
        (integral volume fun t : Real => (1 / rho) *
          (logGaussianEntireKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I) /
            ((sigma : Complex) + (t : Complex) * Complex.I - rho))) := by
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall hPoint)
    _ = (1 / rho) * ((((1 / (2 * Real.pi) : Real) : Complex)) *
        (integral volume fun t : Real =>
          logGaussianEntireKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I) /
            ((sigma : Complex) + (t : Complex) * Complex.I - rho))) := by
      rw [integral_const_mul]
      ring
    _ = _ := by rw [hTail]

theorem logGaussian_xi_paired_integral_eq_tail
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) (p : RiemannXiDivisorZeroIndex) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        (integral volume fun t : Real =>
          logGaussianMellinKernel X V tau ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
            (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
              1 / riemannXiDivisorZeroValue p)) =
      (1 / riemannXiDivisorZeroValue p) *
        logGaussianSpectralTail X V tau 1 (riemannXiDivisorZeroValue p) := by
  have hcast : ((3 / 2 : Real) : Complex) = (3 / 2 : Complex) := by norm_num
  have hRe : (riemannXiDivisorZeroValue p).re < (3 / 2 : Real) :=
    lt_trans (xiDivisorZeroValue_re_bounds p).2 (by norm_num)
  simpa only [hcast] using
    logGaussian_paired_resolvent_integral_eq_tail X V tau (3 / 2)
      (riemannXiDivisorZeroValue p) hX hV (by norm_num)
      (riemannXiDivisorZeroValue_ne_zero p) hRe

theorem logGaussian_xi_physical_tail_summable
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      (1 / riemannXiDivisorZeroValue p) *
        logGaussianSpectralTail X V tau 1 (riemannXiDivisorZeroValue p)) := by
  let C : Complex := (((1 / (2 * Real.pi) : Real) : Complex))
  have hSum := (logGaussian_xi_atoms_summable_norm X V tau hX hV).mul_left (norm C)
  have hInt : Summable (fun p : RiemannXiDivisorZeroIndex =>
      C * integral volume (fun t : Real =>
        logGaussianMellinKernel X V tau ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
          (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p))) := by
    apply Summable.of_norm_bounded hSum
    intro p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg C)
  apply hInt.congr
  intro p
  exact logGaussian_xi_paired_integral_eq_tail X V tau hX hV p

end PrimeFactorOscillations.PrimeClassDeletion
