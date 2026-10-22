/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianFourierKernel

/-!
# Exact normalized log-Gaussian inversion on every vertical line
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianEntireKernel_vertical_integral
    (X V tau y sigma : Real) (hX : 0 < X) (hV : 0 < V) (hy : 0 < y) :
    (integral volume fun t : Real =>
      (y : Complex) ^ (-((sigma : Complex) + (t : Complex) * Complex.I)) *
        logGaussianEntireKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I)) =
      (Real.sqrt (2 * Real.pi * (1 / V)) : Complex) *
        Complex.exp (-(((Real.log X - Real.log y) ^ 2 / (2 * V) : Real) : Complex) +
          (tau : Complex) * Complex.I * ((Real.log X - Real.log y : Real) : Complex)) := by
  have hVc : Not ((V : Complex) = 0) := Complex.ofReal_ne_zero.mpr hV.ne'
  have he :
      (((1 / V : Real) : Complex) / 2 *
        (logGaussianFourierLinear X V tau y sigma) ^ 2) +
          logGaussianFourierConstant X V tau y sigma =
        -(((Real.log X - Real.log y) ^ 2 / (2 * V) : Real) : Complex) +
          (tau : Complex) * Complex.I * ((Real.log X - Real.log y : Real) : Complex) := by
    dsimp [logGaussianFourierLinear, logGaussianFourierConstant]
    push_cast
    field_simp [hVc]
    have hI3 : Complex.I ^ (3 : Nat) = -Complex.I := by
      rw [pow_succ, Complex.I_sq]
      ring
    have hI4 : Complex.I ^ (4 : Nat) = 1 := by
      rw [show (4 : Nat) = 2 + 2 by decide, pow_add, Complex.I_sq]
      norm_num
    ring_nf
    simp only [Complex.I_sq, hI3, hI4]
    ring
  simp_rw [logGaussianEntireKernel_vertical_factor X V tau y sigma _ hX hV hy]
  rw [integral_mul_const,
    logGaussian_unnormalized_moment (1 / V) (one_div_pos.mpr hV),
    mul_assoc, <- Complex.exp_add, he]

theorem logGaussianEntireKernel_inverse_density
    (X V tau y sigma : Real) (hX : 0 < X) (hV : 0 < V) (hy : 0 < y) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        (integral volume fun t : Real =>
          (y : Complex) ^ (-((sigma : Complex) + (t : Complex) * Complex.I)) *
            logGaussianEntireKernel X V tau
              ((sigma : Complex) + (t : Complex) * Complex.I)) =
      (logGaussianDensity V (Real.log y - Real.log X) : Complex) *
        Complex.exp (-(tau : Complex) * Complex.I *
          ((Real.log y - Real.log X : Real) : Complex)) := by
  have hsqrt : Real.sqrt (2 * Real.pi * (1 / V)) *
      Real.sqrt (2 * Real.pi * V) = 2 * Real.pi := by
    rw [<- Real.sqrt_mul (by positivity)]
    have hv : (2 * Real.pi * (1 / V)) * (2 * Real.pi * V) = (2 * Real.pi) ^ 2 := by
      field_simp
    rw [hv, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
  have hn : (1 / (2 * Real.pi) : Real) * Real.sqrt (2 * Real.pi * (1 / V)) =
      1 / Real.sqrt (2 * Real.pi * V) := by
    calc
      (1 / (2 * Real.pi) : Real) * Real.sqrt (2 * Real.pi * (1 / V)) =
          Real.sqrt (2 * Real.pi * (1 / V)) / (2 * Real.pi) := by ring
      _ = _ := (div_eq_div_iff (by positivity) (by positivity)).mpr (by simpa using hsqrt)
  have hnc :
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        (Real.sqrt (2 * Real.pi * (1 / V)) : Complex) =
      1 / (Real.sqrt (2 * Real.pi * V) : Complex) := by
    exact_mod_cast hn
  rw [logGaussianEntireKernel_vertical_integral X V tau y sigma hX hV hy,
    <- mul_assoc, hnc, Complex.exp_add]
  simp only [logGaussianDensity, Complex.ofReal_div, Complex.ofReal_exp]
  have he : -(((Real.log X - Real.log y) ^ 2 / (2 * V) : Real) : Complex) =
      ((-(Real.log y - Real.log X) ^ 2 / (2 * V) : Real) : Complex) := by
    push_cast
    ring
  have hp : (tau : Complex) * Complex.I * ((Real.log X - Real.log y : Real) : Complex) =
      -(tau : Complex) * Complex.I * ((Real.log y - Real.log X : Real) : Complex) := by
    push_cast
    ring
  simp only [Complex.ofReal_div] at he
  rw [he, hp]
  ring

end PrimeFactorOscillations.PrimeClassDeletion
