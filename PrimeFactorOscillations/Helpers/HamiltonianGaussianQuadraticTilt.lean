/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Complex Gaussian moments for the actual quadratic tilt

The precision remains in the right half-plane under the complete
covariance quotient. Integrability and the integration-by-parts recurrence
are proved for the actual Lebesgue integrals, with no assumed Wick law.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory
open scoped Topology

def complexGaussianKernel (b : Complex) (n : Nat) (x : Real) : Complex :=
  (x : Complex) ^ n * Complex.exp (-b * (x : Complex) ^ 2)

def complexGaussianMoment (b : Complex) (n : Nat) : Complex :=
  MeasureTheory.integral MeasureTheory.volume (complexGaussianKernel b n)

theorem complexGaussianKernel_integrable (b : Complex) (hb : 0 < b.re)
    (n : Nat) : MeasureTheory.Integrable (complexGaussianKernel b n) := by
  have hReal : MeasureTheory.Integrable
      (fun x : Real => x ^ n * Real.exp (-b.re * x ^ 2)) := by
    have hn : (-1 : Real) < (n : Real) :=
      lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hb hn)
  have hContinuous : Continuous (complexGaussianKernel b n) :=
    (Complex.continuous_ofReal.pow n).mul
      (Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.pow 2)))
  refine And.intro hContinuous.aestronglyMeasurable ?_
  have hFinite := hReal.hasFiniteIntegral
  rw [<- MeasureTheory.hasFiniteIntegral_norm_iff] at hFinite
  rw [<- MeasureTheory.hasFiniteIntegral_norm_iff]
  convert! hFinite using 1
  simp only [complexGaussianKernel, norm_mul, norm_pow,
    Complex.norm_real, norm_cexp_neg_mul_sq,
    Real.norm_of_nonneg (Real.exp_pos _).le]

theorem complexGaussianMoment_zero (b : Complex) (hb : 0 < b.re) :
    complexGaussianMoment b 0 = (Real.pi / b) ^ (1 / 2 : Complex) := by
  have hKernel : complexGaussianKernel b 0 =
      (fun x : Real => Complex.exp (-b * (x : Complex) ^ 2)) := by
    funext x
    simp only [complexGaussianKernel, pow_zero, one_mul]
  rw [complexGaussianMoment, hKernel]
  exact integral_gaussian_complex hb

theorem complexGaussianMoment_first (b : Complex) (hb : 0 < b.re) :
    complexGaussianMoment b 1 = 0 := by
  have hDeriv : forall x : Real,
      HasDerivAt (fun y : Real => Complex.exp (-b * (y : Complex) ^ 2))
        (-(2 * b) * complexGaussianKernel b 1 x) x := by
    intro x
    have h := (((hasDerivAt_pow 2 (x : Complex)).const_mul (-b)).cexp).comp_ofReal
    convert! h using 1 <;>
      simp only [complexGaussianKernel, pow_one] <;> ring
  have hInt : MeasureTheory.Integrable
      (fun x : Real => -(2 * b) * complexGaussianKernel b 1 x) :=
    (complexGaussianKernel_integrable b hb 1).const_mul _
  have hZero := integral_eq_zero_of_hasDerivAt_of_integrable hDeriv hInt
    (integrable_cexp_neg_mul_sq hb)
  rw [MeasureTheory.integral_const_mul] at hZero
  have hb0 : Not (b = 0) := by
    intro h
    simp only [h, Complex.zero_re] at hb
    exact (lt_irrefl 0) hb
  have hScalar : Not (-(2 * b) = 0) :=
    neg_ne_zero.mpr (mul_ne_zero (by norm_num) hb0)
  exact (mul_eq_zero.mp hZero).resolve_left hScalar

theorem complexGaussianMoment_recurrence (b : Complex) (hb : 0 < b.re)
    (n : Nat) :
    complexGaussianMoment b (n + 2) =
      ((n + 1 : Nat) : Complex) * complexGaussianMoment b n / (2 * b) := by
  let f' : Real -> Complex := fun x =>
    ((n + 1 : Nat) : Complex) * complexGaussianKernel b n x -
      (2 * b) * complexGaussianKernel b (n + 2) x
  have hDeriv : forall x : Real,
      HasDerivAt (complexGaussianKernel b (n + 1)) (f' x) x := by
    intro x
    have h := ((hasDerivAt_pow (n + 1) (x : Complex)).mul
      (((hasDerivAt_pow 2 (x : Complex)).const_mul (-b)).cexp)).comp_ofReal
    convert! h using 1 <;>
      simp only [f', complexGaussianKernel, Nat.add_sub_cancel, pow_one,
        pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  have hLeft := (complexGaussianKernel_integrable b hb n).const_mul
    (((n + 1 : Nat) : Complex))
  have hRight := (complexGaussianKernel_integrable b hb (n + 2)).const_mul (2 * b)
  have hInt : MeasureTheory.Integrable f' := hLeft.sub hRight
  have hZero := integral_eq_zero_of_hasDerivAt_of_integrable hDeriv hInt
    (complexGaussianKernel_integrable b hb (n + 1))
  change MeasureTheory.integral MeasureTheory.volume
    (fun x : Real => ((n + 1 : Nat) : Complex) * complexGaussianKernel b n x -
      (2 * b) * complexGaussianKernel b (n + 2) x) = 0 at hZero
  rw [MeasureTheory.integral_sub hLeft hRight,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hZero
  have hb0 : Not (b = 0) := by
    intro h
    simp only [h, Complex.zero_re] at hb
    exact (lt_irrefl 0) hb
  apply (eq_div_iff (mul_ne_zero (by norm_num) hb0)).2
  calc
    complexGaussianMoment b (n + 2) * (2 * b) =
        (2 * b) * complexGaussianMoment b (n + 2) := mul_comm _ _
    _ = ((n + 1 : Nat) : Complex) * complexGaussianMoment b n :=
      (sub_eq_zero.mp hZero).symm

theorem covarianceQuotient_real_part (z : Complex) (hz : norm z < 1) :
    (1 - 2 * (z / (1 + z)).re) * Complex.normSq (1 + z) =
      1 - Complex.normSq z := by
  have hAdd : Not (1 + z = 0) := by
    intro h
    have hEq : z = -(1 : Complex) := by
      calc
        z = (1 + z) - 1 := by ring
        _ = -1 := by rw [h]; ring
    rw [hEq, norm_neg, norm_one] at hz
    exact (lt_irrefl 1) hz
  have hDen : Not (Complex.normSq (1 + z) = 0) :=
    ne_of_gt (Complex.normSq_pos.mpr hAdd)
  rw [Complex.div_re]
  field_simp [hDen]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, zero_add]
  ring

theorem covarianceQuotient_real_part_lt_half (z : Complex) (hz : norm z < 1) :
    (z / (1 + z)).re < 1 / 2 := by
  have hAdd : Not (1 + z = 0) := by
    intro h
    have hEq : z = -(1 : Complex) := by
      calc
        z = (1 + z) - 1 := by ring
        _ = -1 := by rw [h]; ring
    rw [hEq, norm_neg, norm_one] at hz
    exact (lt_irrefl 1) hz
  have hDen := Complex.normSq_pos.mpr hAdd
  have hSq : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hIdentity := covarianceQuotient_real_part z hz
  nlinarith

def gaussianTiltPrecision (z : Complex) : Complex :=
  (1 - z / (1 + z)) / 2

theorem gaussianTiltPrecision_real_part (z : Complex) (hz : norm z < 1) :
    1 / 4 < (gaussianTiltPrecision z).re := by
  have h := covarianceQuotient_real_part_lt_half z hz
  have hRe : (gaussianTiltPrecision z).re =
      (1 - (z / (1 + z)).re) / 2 := by
    dsimp only [gaussianTiltPrecision]
    norm_num [Complex.div_re, Complex.sub_re, Complex.normSq_apply]
  rw [hRe]
  linarith

theorem tiltedGaussianKernel_integrable (z : Complex) (hz : norm z < 1)
    (n : Nat) :
    MeasureTheory.Integrable (complexGaussianKernel (gaussianTiltPrecision z) n) :=
  complexGaussianKernel_integrable _ (lt_trans (by norm_num)
    (gaussianTiltPrecision_real_part z hz)) n

end PrimeFactorOscillations
