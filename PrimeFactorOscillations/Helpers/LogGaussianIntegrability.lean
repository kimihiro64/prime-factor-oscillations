/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.LogGaussianMellinKernel

/-!
# Integrability of the actual log-Gaussian Mellin kernel

The reciprocal s factor is retained. The vertical line may be any positive
real sigma, and the frequency is arbitrary. No zero-location hypothesis
is required for this kernel estimate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open MeasureTheory Filter

theorem logGaussianMellinKernel_vertical_continuous (X V tau sigma : Real)
    (hX : 0 < X) (hsigma : 0 < sigma) :
    Continuous (fun t : Real =>
      logGaussianMellinKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I)) := by
  let l : Real -> Complex := fun t => (sigma : Complex) + (t : Complex) * Complex.I
  have hl : Continuous l := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hlog : Continuous (fun t : Real => Complex.log (X : Complex) * l t) :=
    continuous_const.mul hl
  have hp : Continuous (fun t : Real => (X : Complex) ^ l t) := by
    simpa only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne')]
      using hlog.cexp
  have he : Continuous (fun t : Real => Complex.exp ((V : Complex) / 2 *
      (l t - (tau : Complex) * Complex.I) ^ 2)) :=
    (continuous_const.mul ((hl.sub continuous_const).pow 2)).cexp
  have hne (t : Real) : Not (l t = 0) := by
    intro h
    have hre := congrArg Complex.re h
    have hs : (l t).re = sigma := by simp [l]
    rw [hs, Complex.zero_re] at hre
    linarith only [hre, hsigma]
  exact (hp.mul he).div hl hne

theorem logGaussianMellinKernel_integrable_vertical (X V tau sigma : Real)
    (hX : 0 < X) (hV : 0 < V) (hsigma : 0 < sigma) :
    Integrable (fun t : Real =>
      logGaussianMellinKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I)) := by
  let B := X ^ sigma * Real.exp (V * sigma ^ 2 / 2)
  let K := B / sigma
  have hB : 0 <= B := mul_nonneg (Real.rpow_pos_of_pos hX sigma).le (Real.exp_pos _).le
  have hG : Integrable (fun t : Real => Real.exp (-(V / 2) * (t - tau) ^ 2)) :=
    (integrable_exp_neg_mul_sq (div_pos hV (by norm_num))).comp_sub_right tau
  have hMajor : Integrable (fun t : Real => K * Real.exp (-(V / 2) * (t - tau) ^ 2)) :=
    hG.const_mul K
  apply hMajor.mono' (logGaussianMellinKernel_vertical_continuous X V tau sigma hX hsigma).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have hN : sigma <= norm ((sigma : Complex) + (t : Complex) * Complex.I) := by
    have h := Complex.abs_re_le_norm ((sigma : Complex) + (t : Complex) * Complex.I)
    have hre : ((sigma : Complex) + (t : Complex) * Complex.I).re = sigma := by simp
    rw [hre] at h
    exact (le_abs_self sigma).trans h
  rw [logGaussianMellinKernel_vertical_norm_factor X V tau sigma t hX]
  change B * Real.exp (-(V / 2) * (t - tau) ^ 2) /
      norm ((sigma : Complex) + (t : Complex) * Complex.I) <=
    K * Real.exp (-(V / 2) * (t - tau) ^ 2)
  calc
    _ <= B * Real.exp (-(V / 2) * (t - tau) ^ 2) / sigma :=
      div_le_div_of_nonneg_left (mul_nonneg hB (Real.exp_pos _).le) hsigma hN
    _ = _ := by dsimp [K]; ring

end PrimeFactorOscillations.PrimeClassDeletion
