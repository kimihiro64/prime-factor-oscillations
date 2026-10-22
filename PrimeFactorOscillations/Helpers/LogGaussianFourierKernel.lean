/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianMellinKernel
import PrimeFactorOscillations.Helpers.LogGaussianMoment

/-!
# Exact vertical inversion of the entire log-Gaussian kernel

All positive X,V,y, all real vertical lines and all real frequencies are
retained. This density inversion is the input to the existing absolute
resolvent-tail pairing; the reciprocal s is restored in that consumer.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianEntireKernel (X V tau : Real) (s : Complex) : Complex :=
  (X : Complex) ^ s *
    Complex.exp ((V : Complex) / 2 * (s - (tau : Complex) * Complex.I) ^ 2)

noncomputable def logGaussianFourierLinear (X V tau y sigma : Real) : Complex :=
  Complex.I * (((Real.log X - Real.log y : Real) : Complex) +
    (V : Complex) * ((sigma : Complex) - (tau : Complex) * Complex.I))

noncomputable def logGaussianFourierConstant (X V tau y sigma : Real) : Complex :=
  ((Real.log X - Real.log y : Real) : Complex) * (sigma : Complex) +
    (V : Complex) / 2 * ((sigma : Complex) - (tau : Complex) * Complex.I) ^ 2

theorem logGaussianEntireKernel_vertical_factor
    (X V tau y sigma t : Real) (hX : 0 < X) (hV : 0 < V) (hy : 0 < y) :
    (y : Complex) ^ (-((sigma : Complex) + (t : Complex) * Complex.I)) *
        logGaussianEntireKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I) =
      Complex.exp (((-(1 / (2 * (1 / V))) : Real) : Complex) * (t : Complex) ^ 2 +
        logGaussianFourierLinear X V tau y sigma * (t : Complex)) *
          Complex.exp (logGaussianFourierConstant X V tau y sigma) := by
  have hXc : Not ((X : Complex) = 0) := Complex.ofReal_ne_zero.mpr hX.ne'
  have hyc : Not ((y : Complex) = 0) := Complex.ofReal_ne_zero.mpr hy.ne'
  have hVc : Not ((V : Complex) = 0) := Complex.ofReal_ne_zero.mpr hV.ne'
  simp only [logGaussianEntireKernel, Complex.cpow_def_of_ne_zero hXc,
    Complex.cpow_def_of_ne_zero hyc, <- Complex.exp_add,
    <- Complex.ofReal_log hX.le, <- Complex.ofReal_log hy.le]
  congr 1
  dsimp [logGaussianFourierLinear, logGaussianFourierConstant]
  push_cast
  field_simp [hVc]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem logGaussianEntireKernel_vertical_integrable
    (X V tau y sigma : Real) (hX : 0 < X) (hV : 0 < V) (hy : 0 < y) :
    Integrable (fun t : Real =>
      (y : Complex) ^ (-((sigma : Complex) + (t : Complex) * Complex.I)) *
        logGaussianEntireKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I)) := by
  have hb : (((-(1 / (2 * (1 / V))) : Real) : Complex)).re < 0 := by
    change -(1 / (2 * (1 / V))) < 0
    exact neg_lt_zero.mpr (one_div_pos.mpr (mul_pos (by norm_num) (one_div_pos.mpr hV)))
  have hBase := integrable_cexp_quadratic' hb (logGaussianFourierLinear X V tau y sigma) 0
  have h := hBase.mul_const (Complex.exp (logGaussianFourierConstant X V tau y sigma))
  apply h.congr
  filter_upwards with t
  simpa only [add_zero] using
    (logGaussianEntireKernel_vertical_factor X V tau y sigma t hX hV hy).symm

end PrimeFactorOscillations.PrimeClassDeletion
