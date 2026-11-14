/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.MeasureTheory.Integral.Pi
import PrimeFactorOscillations.Helpers.HamiltonianGaussianPolynomialTilt

/-! # Finite-dimensional Gaussian quadratic reweighting

The exact integral of every finite signed sum of tensor monomials is
computed against the full complex quadratic tilt. Fubini and integrability
are discharged from the scalar Gaussian theorem, in arbitrary dimension.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory

variable {Iota Term : Type*} [Fintype Iota] [DecidableEq Iota]

def gaussianTensorMeasure : MeasureTheory.Measure (Iota -> Real) :=
  MeasureTheory.Measure.pi (fun _ : Iota => MeasureTheory.volume)

def gaussianTensorTiltKernel (z w : Iota -> Complex) (d : Iota -> Nat)
    (x : Iota -> Real) : Complex :=
  Finset.prod Finset.univ (fun i =>
    (w i * (x i : Complex)) ^ d i *
      Complex.exp (-gaussianTiltPrecision (z i) * (x i : Complex) ^ 2))

def gaussianTensorTiltNormalizer (z : Iota -> Complex) : Complex :=
  Finset.prod Finset.univ (fun i => complexGaussianMoment (gaussianTiltPrecision (z i)) 0)

private theorem tensor_scalar_factor (z w : Complex) (d : Nat) :
    (fun x : Real => (w * (x : Complex)) ^ d *
      Complex.exp (-gaussianTiltPrecision z * (x : Complex) ^ 2)) =
    (fun x : Real => w ^ d * complexGaussianKernel (gaussianTiltPrecision z) d x) := by
  funext x
  rw [mul_pow]
  unfold complexGaussianKernel
  ring

theorem gaussianTensorTiltKernel_integrable (z w : Iota -> Complex)
    (hz : forall i, norm (z i) < 1) (d : Iota -> Nat) :
    MeasureTheory.Integrable (gaussianTensorTiltKernel z w d) gaussianTensorMeasure := by
  unfold gaussianTensorTiltKernel gaussianTensorMeasure
  apply MeasureTheory.Integrable.fintype_prod
    (f := fun i (x : Real) => (w i * (x : Complex)) ^ d i *
      Complex.exp (-gaussianTiltPrecision (z i) * (x : Complex) ^ 2))
  intro i
  rw [tensor_scalar_factor]
  exact (tiltedGaussianKernel_integrable (z i) (hz i) (d i)).const_mul (w i ^ d i)

theorem gaussianTensorTiltKernel_integral (z w : Iota -> Complex) (d : Iota -> Nat) :
    MeasureTheory.integral gaussianTensorMeasure (gaussianTensorTiltKernel z w d) =
      Finset.prod Finset.univ (fun i => w i ^ d i *
        complexGaussianMoment (gaussianTiltPrecision (z i)) (d i)) := by
  unfold gaussianTensorTiltKernel gaussianTensorMeasure
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun i (x : Real) => (w i * (x : Complex)) ^ d i *
      Complex.exp (-gaussianTiltPrecision (z i) * (x : Complex) ^ 2))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [tensor_scalar_factor, MeasureTheory.integral_const_mul]
  rfl

theorem gaussianTensorTiltNormalizer_nonzero (z : Iota -> Complex)
    (hz : forall i, norm (z i) < 1) :
    Not (gaussianTensorTiltNormalizer z = 0) := by
  unfold gaussianTensorTiltNormalizer
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact complexGaussianMoment_zero_nonzero _
    (lt_trans (by norm_num) (gaussianTiltPrecision_real_part (z i) (hz i)))

theorem gaussianTensorTiltKernel_normalized (z w : Iota -> Complex)
    (hz : forall i, norm (z i) < 1)
    (hw : forall i, w i ^ 2 = z i / (1 + z i)) (d : Iota -> Nat) :
    MeasureTheory.integral gaussianTensorMeasure (gaussianTensorTiltKernel z w d) /
        gaussianTensorTiltNormalizer z =
      Finset.prod Finset.univ (fun i => gaussianWickMonomial (z i) (d i)) := by
  rw [gaussianTensorTiltKernel_integral, gaussianTensorTiltNormalizer,
    <- Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact gaussianTilt_monomial_moment (z i) (hz i) (w i) (hw i) (d i)

def gaussianTensorPolynomialTiltKernel (z w : Iota -> Complex)
    (S : Finset Term) (c : Term -> Complex) (d : Term -> Iota -> Nat)
    (x : Iota -> Real) : Complex :=
  Finset.sum S (fun t => c t * gaussianTensorTiltKernel z w (d t) x)

theorem gaussianTensorPolynomialTiltKernel_integrable (z w : Iota -> Complex)
    (hz : forall i, norm (z i) < 1) (S : Finset Term)
    (c : Term -> Complex) (d : Term -> Iota -> Nat) :
    MeasureTheory.Integrable (gaussianTensorPolynomialTiltKernel z w S c d)
      gaussianTensorMeasure := by
  unfold gaussianTensorPolynomialTiltKernel
  exact MeasureTheory.integrable_finsetSum S
    (fun t _ => (gaussianTensorTiltKernel_integrable z w hz (d t)).const_mul (c t))

theorem gaussianTensorPolynomialTilt_normalized (z w : Iota -> Complex)
    (hz : forall i, norm (z i) < 1)
    (hw : forall i, w i ^ 2 = z i / (1 + z i))
    (S : Finset Term) (c : Term -> Complex) (d : Term -> Iota -> Nat) :
    MeasureTheory.integral gaussianTensorMeasure
        (gaussianTensorPolynomialTiltKernel z w S c d) /
        gaussianTensorTiltNormalizer z =
      Finset.sum S (fun t => c t *
        Finset.prod Finset.univ (fun i => gaussianWickMonomial (z i) (d t i))) := by
  unfold gaussianTensorPolynomialTiltKernel
  rw [MeasureTheory.integral_finsetSum S
    (fun t _ => (gaussianTensorTiltKernel_integrable z w hz (d t)).const_mul (c t)),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t ht
  rw [MeasureTheory.integral_const_mul, mul_div_assoc,
    gaussianTensorTiltKernel_normalized z w hz hw (d t)]

theorem gaussianTensorPolynomialTilt_integral (z w : Iota -> Complex)
    (hz : forall i, norm (z i) < 1)
    (hw : forall i, w i ^ 2 = z i / (1 + z i))
    (S : Finset Term) (c : Term -> Complex) (d : Term -> Iota -> Nat) :
    MeasureTheory.integral gaussianTensorMeasure
        (gaussianTensorPolynomialTiltKernel z w S c d) =
      gaussianTensorTiltNormalizer z *
        Finset.sum S (fun t => c t *
          Finset.prod Finset.univ (fun i => gaussianWickMonomial (z i) (d t i))) := by
  have h := gaussianTensorPolynomialTilt_normalized z w hz hw S c d
  have hEq := (div_eq_iff (gaussianTensorTiltNormalizer_nonzero z hz)).mp h
  exact hEq.trans (mul_comm _ _)

end PrimeFactorOscillations
