/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.Ring

/-!
# The exact Mellin kernel for the log-Gaussian prime-error probe

This is the actual complex kernel, including its reciprocal s factor.
The vertical norm retains the shifted frequency and the full variance.
The physical Perron identity and its contour shift remain separate steps.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianMellinKernel (X V tau : Real) (s : Complex) : Complex :=
  (X : Complex) ^ s * Complex.exp ((V : Complex) / 2 *
    (s - (tau : Complex) * Complex.I) ^ 2) / s

theorem logGaussianMellinKernel_vertical_norm (X V tau sigma t : Real) (hX : 0 < X) :
    norm (logGaussianMellinKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I)) =
      X ^ sigma * Real.exp (V / 2 * (sigma ^ 2 - (t - tau) ^ 2)) /
        norm ((sigma : Complex) + (t : Complex) * Complex.I) := by
  have hs : ((sigma : Complex) + (t : Complex) * Complex.I).re = sigma := by simp
  have he : ((V : Complex) / 2 *
      (((sigma : Complex) + (t : Complex) * Complex.I) - (tau : Complex) * Complex.I) ^ 2).re =
      V / 2 * (sigma ^ 2 - (t - tau) ^ 2) := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
  rw [logGaussianMellinKernel, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hX, Complex.norm_exp, hs, he]

theorem logGaussianMellinKernel_vertical_norm_factor (X V tau sigma t : Real) (hX : 0 < X) :
    norm (logGaussianMellinKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I)) =
      X ^ sigma * Real.exp (V * sigma ^ 2 / 2) * Real.exp (-(V / 2) * (t - tau) ^ 2) /
        norm ((sigma : Complex) + (t : Complex) * Complex.I) := by
  rw [logGaussianMellinKernel_vertical_norm X V tau sigma t hX,
    show V / 2 * (sigma ^ 2 - (t - tau) ^ 2) =
      V * sigma ^ 2 / 2 + -(V / 2) * (t - tau) ^ 2 by ring,
    Real.exp_add]
  ring

end PrimeFactorOscillations.PrimeClassDeletion
