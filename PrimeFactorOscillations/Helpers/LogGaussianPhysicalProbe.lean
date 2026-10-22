/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPhysicalPerron
import PrimeFactorOscillations.Helpers.LogGaussianSignedIdentity

/-!
# The physical centered Gaussian probe and its full signed xi identity

The probe is the actual integral of psi(X*exp(u))-X*exp(u).
The Gaussian reference term, all multiplicity-counted paired zero terms,
the reference pole, the constant and the gamma contribution are retained.
The asymptotic residue expansion and its remainder remain separate steps.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianPsiProbe (X V tau : Real) : Complex :=
  integral volume fun u : Real =>
    ((Chebyshev.psi (X * Real.exp u) - X * Real.exp u : Real) : Complex) *
      logGaussianWave V tau u

theorem logGaussian_reference_factor (X V tau u : Real) :
    ((X * Real.exp u : Real) : Complex) * logGaussianWave V tau u =
      (X : Complex) * ((logGaussianDensity V u : Complex) *
        Complex.exp (((1 : Complex) - (tau : Complex) * Complex.I) * (u : Complex))) := by
  rw [logGaussianWave, Complex.ofReal_mul]
  have he : ((1 : Complex) - (tau : Complex) * Complex.I) * (u : Complex) =
      (u : Complex) + (-(tau : Complex) * Complex.I * (u : Complex)) := by ring
  rw [he, Complex.exp_add, <- Complex.ofReal_exp]
  ring

theorem logGaussian_reference_integrable (X V tau : Real) (hV : 0 < V) :
    Integrable (fun u : Real =>
      ((X * Real.exp u : Real) : Complex) * logGaussianWave V tau u) := by
  have h := (logGaussianDensity_integrable_complex_moment V hV
    ((1 : Complex) - (tau : Complex) * Complex.I)).const_mul (X : Complex)
  apply h.congr
  exact Filter.Eventually.of_forall fun u => (logGaussian_reference_factor X V tau u).symm

theorem logGaussian_reference_integral (X V tau : Real) (hV : 0 < V) :
    (integral volume fun u : Real =>
      ((X * Real.exp u : Real) : Complex) * logGaussianWave V tau u) =
        (X : Complex) * Complex.exp ((V : Complex) / 2 *
          ((1 : Complex) - (tau : Complex) * Complex.I) ^ 2) := by
  simp_rw [logGaussian_reference_factor]
  rw [integral_const_mul, logGaussianDensity_complex_moment V hV]

theorem logGaussianPsiProbe_integrable (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    Integrable (fun u : Real =>
      ((Chebyshev.psi (X * Real.exp u) - X * Real.exp u : Real) : Complex) *
        logGaussianWave V tau u) := by
  have hPsi := logGaussian_physical_psi_integrable X V tau hX hV
  have hRef := logGaussian_reference_integrable X V tau hV
  apply (hPsi.sub hRef).congr
  filter_upwards with u
  dsimp only [Pi.sub_apply]
  push_cast
  ring

theorem logGaussianPsiProbe_eq_safeLineIntegral
    (X V tau sigma : Real) (hX : 0 < X) (hV : 0 < V) (hSigma : 1 < sigma) :
    logGaussianPsiProbe X V tau =
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        (integral volume fun t : Real =>
          (-deriv riemannZeta ((sigma : Complex) + (t : Complex) * Complex.I) /
            riemannZeta ((sigma : Complex) + (t : Complex) * Complex.I)) *
              logGaussianMellinKernel X V tau
                ((sigma : Complex) + (t : Complex) * Complex.I)) -
      (X : Complex) * Complex.exp ((V : Complex) / 2 *
        ((1 : Complex) - (tau : Complex) * Complex.I) ^ 2) := by
  have hPsi := logGaussian_physical_psi_integrable X V tau hX hV
  have hRef := logGaussian_reference_integrable X V tau hV
  have he : (fun u : Real =>
      ((Chebyshev.psi (X * Real.exp u) - X * Real.exp u : Real) : Complex) *
        logGaussianWave V tau u) =
    (fun u : Real => (Chebyshev.psi (X * Real.exp u) : Complex) * logGaussianWave V tau u -
      ((X * Real.exp u : Real) : Complex) * logGaussianWave V tau u) := by
    funext u
    push_cast
    ring
  rw [logGaussianPsiProbe, he, integral_sub hPsi hRef,
    logGaussian_physical_psi_eq_safeLineIntegral X V tau sigma hX hV hSigma,
    logGaussian_reference_integral X V tau hV]

theorem logGaussianPsiProbe_eq_full_signed_xi_identity
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    let H : Real -> Complex := logGaussianVerticalKernel X V tau
    logGaussianPsiProbe X V tau =
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        (logGaussianXiConstant * integral volume H -
          tsum (fun p : RiemannXiDivisorZeroIndex => integral volume (fun t : Real =>
            H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
              1 / riemannXiDivisorZeroValue p))) +
          integral volume (fun t : Real => H t /
            ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1)) +
          integral volume (fun t : Real => H t * logGaussianGammaMultiplier t)) -
      (X : Complex) * Complex.exp ((V : Complex) / 2 *
        ((1 : Complex) - (tau : Complex) * Complex.I) ^ 2) := by
  have hcast : ((3 / 2 : Real) : Complex) = (3 / 2 : Complex) := by norm_num
  have hPhys := logGaussianPsiProbe_eq_safeLineIntegral X V tau (3 / 2) hX hV (by norm_num)
  simp only [hcast] at hPhys
  have hSigned := (logGaussian_safeLine_signed_identity X V tau hX hV).2
  dsimp only [logGaussianVerticalKernel] at hSigned
  dsimp only [logGaussianVerticalKernel]
  rw [hPhys, hSigned]

end PrimeFactorOscillations.PrimeClassDeletion
