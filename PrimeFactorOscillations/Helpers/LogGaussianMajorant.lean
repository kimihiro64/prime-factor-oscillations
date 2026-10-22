/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.GaussianScalarMajorant
import PrimeFactorOscillations.Helpers.LogGaussianIntegrability

/-!
# A complete inverse-square safe-line majorant for the log-Gaussian test

The constant retains X, the variance, frequency and vertical-line position.
Its purpose is absolute integrated summability before the signed xi-series
interchange, not an estimate discarding the signed prime-error signal.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianMajorant (X V tau sigma : Real) : Real :=
  X ^ sigma * Real.exp (V * sigma ^ 2 / 2) *
    (abs sigma + abs tau + 1 + 1 / (V / 2))

theorem logGaussianMajorant_pos (X V tau sigma : Real) (hX : 0 < X) (hV : 0 < V) :
    0 < logGaussianMajorant X V tau sigma := by
  unfold logGaussianMajorant
  apply mul_pos (mul_pos (Real.rpow_pos_of_pos hX sigma) (Real.exp_pos _))
  have hi : 0 <= 1 / (V / 2) := div_nonneg (by norm_num) (by linarith only [hV])
  linarith only [abs_nonneg sigma, abs_nonneg tau, hi]

theorem logGaussianMellinKernel_inverse_square_bound (X V tau sigma t : Real)
    (hX : 0 < X) (hV : 0 < V) (hsigma : 0 < sigma) :
    norm (logGaussianMellinKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I)) <=
      logGaussianMajorant X V tau sigma *
        (Inv.inv (norm ((sigma : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat) := by
  let N := norm ((sigma : Complex) + (t : Complex) * Complex.I)
  let B := X ^ sigma * Real.exp (V * sigma ^ 2 / 2)
  let G := Real.exp (-((V / 2) * (t - tau) ^ 2))
  let C0 := abs sigma + abs tau
  have hN : sigma <= N := by
    have h := Complex.abs_re_le_norm ((sigma : Complex) + (t : Complex) * Complex.I)
    have hre : ((sigma : Complex) + (t : Complex) * Complex.I).re = sigma := by simp
    rw [hre] at h
    exact (le_abs_self sigma).trans h
  have hNpos : 0 < N := hsigma.trans_le hN
  have hB : 0 <= B := mul_nonneg (Real.rpow_pos_of_pos hX sigma).le (Real.exp_pos _).le
  have hG : 0 <= G := (Real.exp_pos _).le
  have hC0 : 0 <= C0 := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have ht : abs t <= abs tau + abs (t - tau) := by
    calc
      abs t = abs (tau + (t - tau)) := by congr 1; ring
      _ <= _ := by simpa only [Real.norm_eq_abs] using (norm_add_le tau (t - tau))
  have hS : N <= C0 + abs (t - tau) := by
    have htriangle := norm_add_le (sigma : Complex) ((t : Complex) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs] at htriangle
    dsimp [N, C0]
    linarith only [htriangle, ht]
  have hrow : G * N <= C0 + 1 + 1 / (V / 2) := by
    calc
      G * N <= G * (C0 + abs (t - tau)) := mul_le_mul_of_nonneg_left hS hG
      _ = (C0 + abs (t - tau)) * G := by ring
      _ <= _ := linear_gaussian_le (V / 2) C0 (t - tau)
        (div_pos hV (by norm_num)) hC0
  have hid : norm (logGaussianMellinKernel X V tau
      ((sigma : Complex) + (t : Complex) * Complex.I)) * N ^ 2 = B * G * N := by
    rw [logGaussianMellinKernel_vertical_norm_factor X V tau sigma t hX]
    simp only [neg_mul]
    change (B * G / N) * N ^ 2 = B * G * N
    field_simp [ne_of_gt hNpos]
  have hpoly : norm (logGaussianMellinKernel X V tau
      ((sigma : Complex) + (t : Complex) * Complex.I)) * N ^ 2 <=
      logGaussianMajorant X V tau sigma := by
    rw [hid]
    calc
      B * G * N = B * (G * N) := by ring
      _ <= B * (C0 + 1 + 1 / (V / 2)) := mul_le_mul_of_nonneg_left hrow hB
      _ = _ := rfl
  change norm (logGaussianMellinKernel X V tau
      ((sigma : Complex) + (t : Complex) * Complex.I)) <=
    logGaussianMajorant X V tau sigma * (Inv.inv N) ^ 2
  calc
    _ = (norm (logGaussianMellinKernel X V tau
        ((sigma : Complex) + (t : Complex) * Complex.I)) * N ^ 2) * (Inv.inv N) ^ 2 := by
      field_simp [ne_of_gt hNpos]
    _ <= _ := mul_le_mul_of_nonneg_right hpoly (sq_nonneg _)

end PrimeFactorOscillations.PrimeClassDeletion
