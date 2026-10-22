/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianExposure

/-!
# Exact multiplicity amplitudes and logarithmic Gaussian residue norms

The norm of each actual residue is its positive analytic multiplicity
amplitude times X to its exact Gaussian score. No frequency or phase
is dropped from the complex residue identity.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def gaussianZetaAmplitude (z : ZetaDistinctZero) : Real :=
  norm (((analyticOrderAt riemannZeta z.val).toNat : Complex) / z.val)

theorem gaussianZetaAmplitude_pos (z : ZetaDistinctZero) : 0 < gaussianZetaAmplitude z :=
  norm_pos_iff.mpr (zetaDistinctZero_coefficient_ne_zero z)

theorem gaussianZetaAmplitude_eq (z : ZetaDistinctZero) :
    gaussianZetaAmplitude z = ((analyticOrderAt riemannZeta z.val).toNat : Real) /
      norm z.val := by
  unfold gaussianZetaAmplitude
  rw [norm_div, Complex.norm_natCast]

theorem logGaussianZetaResidue_log_scale_norm
    (X c tau : Real) (z : ZetaDistinctZero) (hX : 0 < X) :
    norm (logGaussianZetaResidue X (c * Real.log X) tau z) =
      gaussianZetaAmplitude z * X ^ (gaussianZeroExponent c z.val.re z.val.im tau) := by
  have hV : ((c * Real.log X : Real) : Complex) / 2 =
      (((c * Real.log X) / 2 : Real) : Complex) := by norm_cast
  have hRealPart :
      (((c * Real.log X : Real) : Complex) / 2 *
        (z.val - (tau : Complex) * Complex.I) ^ 2).re =
      Real.log X * (c / 2 * (z.val.re ^ 2 - (z.val.im - tau) ^ 2)) := by
    rw [hV]
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hMomentNorm :
      norm (Complex.exp (((c * Real.log X : Real) : Complex) / 2 *
        (z.val - (tau : Complex) * Complex.I) ^ 2)) =
      X ^ (c / 2 * (z.val.re ^ 2 - (z.val.im - tau) ^ 2)) := by
    rw [Complex.norm_exp, hRealPart, Real.rpow_def_of_pos hX]
  rw [logGaussianZetaResidue, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hX, hMomentNorm]
  change gaussianZetaAmplitude z * X ^ z.val.re *
      X ^ (c / 2 * (z.val.re ^ 2 - (z.val.im - tau) ^ 2)) = _
  rw [mul_assoc, <- Real.rpow_add hX]
  rfl

end PrimeFactorOscillations.PrimeClassDeletion
