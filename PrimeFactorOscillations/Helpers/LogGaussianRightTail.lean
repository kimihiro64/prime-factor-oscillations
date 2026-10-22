/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPhysicalSpectralTail

/-!
# Uniform right-tail bounds for the negative even Gaussian atoms

Only the archimedean remainder is bounded in modulus. The actual full
spectral-tail identity, including its logarithmic endpoint, is used.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussian_right_weighted_integral_norm_bound
    (V tau a : Real) (rho : Complex) (hV : 0 < V) (hRe : rho.re < -1) :
    norm (integral (volume.restrict (Ioi a)) (logGaussianWeightedWave V tau rho)) <=
      -logGaussianTailScale V * Real.exp ((rho.re + 1) * a) / (rho.re + 1) := by
  have hc : rho.re + 1 < 0 := by linarith only [hRe]
  have hF := (logGaussianWeightedWave_integrable V tau rho hV).integrableOn (s := Ioi a)
  have hM := (integrableOn_exp_mul_Ioi hc a).const_mul (logGaussianTailScale V)
  calc
    _ <= integral (volume.restrict (Ioi a)) (fun u : Real =>
        norm (logGaussianWeightedWave V tau rho u)) := norm_integral_le_integral_norm _
    _ <= integral (volume.restrict (Ioi a)) (fun u : Real =>
        logGaussianTailScale V * Real.exp ((rho.re + 1) * u)) := by
      apply integral_mono_ae hF.norm hM
      exact Filter.Eventually.of_forall fun u =>
        logGaussianWeightedWave_norm_le_left_exponential V tau u rho hV
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi hc a]
      ring

theorem logGaussianSpectralTail_norm_bound_negative
    (X V tau : Real) (rho : Complex) (hX : 0 < X) (hV : 0 < V)
    (hRe : rho.re < -1) :
    norm (logGaussianSpectralTail X V tau 1 rho) <=
      logGaussianTailScale V / (X * (-rho.re - 1)) := by
  let c : Real := rho.re + 1
  let a : Real := -Real.log X
  have hPower : X ^ rho.re * Real.exp (c * a) = 1 / X := by
    rw [Real.rpow_def_of_pos hX, <- Real.exp_add]
    have he : Real.log X * rho.re + c * a = -Real.log X := by dsimp [c, a]; ring
    rw [he, Real.exp_neg, Real.exp_log hX, one_div]
  rw [logGaussianSpectralTail_eq_physical_spectral_tail X V tau rho hX,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
  calc
    _ <= X ^ rho.re *
        (-logGaussianTailScale V * Real.exp (c * a) / c) :=
      mul_le_mul_of_nonneg_left
        (logGaussian_right_weighted_integral_norm_bound V tau a rho hV hRe)
        (Real.rpow_nonneg hX.le _)
    _ = -logGaussianTailScale V * (X ^ rho.re * Real.exp (c * a)) / c := by ring
    _ = logGaussianTailScale V / (X * (-rho.re - 1)) := by
      rw [hPower]
      dsimp only [c]
      have hc : Not (rho.re + 1 = 0) := by linarith only [hRe]
      have hn : Not (-rho.re - 1 = 0) := by linarith only [hRe]
      field_simp [hX.ne', hc, hn]
      <;> ring

theorem logGaussian_negative_even_atom_norm_bound
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) (k : Nat) :
    norm (logGaussianSpectralTail X V tau 1 (-(2 * ((k : Complex) + 1))) /
      (2 * ((k : Complex) + 1))) <=
      (logGaussianTailScale V / X) *
        (1 / ((2 * ((k : Real) + 1)) * (2 * ((k : Real) + 1) - 1))) := by
  let u : Real := 2 * ((k : Real) + 1)
  have hu : 0 < u := by dsimp only [u]; positivity
  have huCast : (u : Complex) = 2 * ((k : Complex) + 1) := by
    dsimp only [u]
    push_cast
    ring
  have hRe : (-(u : Complex)).re < -1 := by
    simp only [Complex.neg_re, Complex.ofReal_re]
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    dsimp only [u]
    linarith
  have hTail := logGaussianSpectralTail_norm_bound_negative X V tau (-(u : Complex))
    hX hV hRe
  simp only [Complex.neg_re, Complex.ofReal_re, neg_neg] at hTail
  rw [<- huCast, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  calc
    _ <= (logGaussianTailScale V / (X * (u - 1))) / u :=
      div_le_div_of_nonneg_right hTail hu.le
    _ = _ := by
      change (logGaussianTailScale V / (X * (u - 1))) / u =
        (logGaussianTailScale V / X) * (1 / (u * (u - 1)))
      have huOne : 0 < u - 1 := by
        dsimp only [u]
        have hk : 0 <= (k : Real) := Nat.cast_nonneg k
        linarith
      field_simp [hX.ne', hu.ne', huOne.ne']

end PrimeFactorOscillations.PrimeClassDeletion
