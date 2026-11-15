/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianProductTails

/-! # The actual Gaussian affine polynomial and its analytic envelope

The exact complex normalization is identified with the positive real
standard Gaussian normalization. The full affine polynomial is retained;
the norm bound below is only its analytic Cauchy-tail input.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory

theorem standardGaussianMoment_zero_real :
    complexGaussianMoment (gaussianTiltPrecision 0) 0 =
      (realStandardGaussianNormalizer : Complex) := by
  have hKernel : complexGaussianKernel (gaussianTiltPrecision 0) 0 =
      fun x : Real => (Real.exp (-((1 - (0 : Real)) / 2) * x ^ 2) : Complex) := by
    funext x
    simp only [complexGaussianKernel, pow_zero, one_mul, gaussianTiltPrecision]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    norm_num
  rw [complexGaussianMoment, hKernel, _root_.integral_complex_ofReal]
  change (realQuadraticGaussianIntegral 0 : Complex) = _
  rw [realQuadraticGaussianIntegral_zero]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem standardGaussianTensor_normalizer_real :
    gaussianTensorTiltNormalizer (fun _ : Iota => 0) =
      ((realStandardGaussianNormalizer ^ Fintype.card Iota : Real) : Complex) := by
  simp only [gaussianTensorTiltNormalizer, standardGaussianMoment_zero_real,
    Finset.prod_const, Finset.card_univ]
  push_cast
  rfl

def realGaussianAffinePolynomial (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (c : Complex) : MvPolynomial Iota Complex :=
  Finset.prod Finset.univ (fun i =>
    1 + MvPolynomial.C c * gaussianLinearForm (realGaussianEigenRows M hM i))

theorem realGaussianAffinePolynomial_eval (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (c : Complex) (x : Iota -> Real) :
    MvPolynomial.eval
        (fun j => complexGaussianSquareRoot (realGaussianEigenVariances M hM j) *
          (x j : Complex)) (realGaussianAffinePolynomial M hM c) =
      Finset.prod Finset.univ (fun i => 1 + c * realGaussianVector M hM x i) := by
  simp only [realGaussianAffinePolynomial, map_prod, map_add, map_one, map_mul,
    MvPolynomial.eval_C, gaussianLinearForm, map_sum, MvPolynomial.eval_X]
  apply Finset.prod_congr rfl
  intro i hi
  congr 2
  unfold realGaussianVector realGaussianEigenRows realGaussianEigenVariances
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem standardGaussianPolynomialKernel_affine (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (c : Complex) (x : Iota -> Real) :
    standardGaussianPolynomialKernel (realGaussianEigenVariances M hM)
        (realGaussianAffinePolynomial M hM c) x =
      Finset.prod Finset.univ (fun i => 1 + c * realGaussianVector M hM x i) *
        ((Finset.prod Finset.univ (fun j => Real.exp (-(1 / 2 : Real) * x j ^ 2)) : Real) :
          Complex) := by
  unfold standardGaussianPolynomialKernel gaussianMvTiltKernel
  rw [realGaussianAffinePolynomial_eval]
  congr 1
  push_cast
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  simp only [gaussianTiltPrecision]
  push_cast
  ring

theorem standardGaussianPolynomialKernel_affine_norm (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (c : Complex) (x : Iota -> Real) :
    norm (standardGaussianPolynomialKernel (realGaussianEigenVariances M hM)
      (realGaussianAffinePolynomial M hM c) x) =
      realGaussianAffineProductKernel M hM c x := by
  rw [standardGaussianPolynomialKernel_affine, norm_mul, norm_prod]
  unfold realGaussianAffineProductKernel
  rw [Complex.norm_real,
    Real.norm_of_nonneg (Finset.prod_nonneg (fun j _ => (Real.exp_pos _).le))]

theorem realGaussianAffinePolynomial_state_norm_le (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (c : Complex) :
    norm (gaussianPolynomialState (realGaussianEigenVariances M hM)
      (realGaussianAffinePolynomial M hM c)) <=
      realGaussianAffineProductAverage M hM c := by
  rw [<- standardGaussianPolynomial_normalized, norm_div,
    standardGaussianTensor_normalizer_real]
  have hZ : 0 <= realStandardGaussianNormalizer ^ Fintype.card Iota :=
    pow_nonneg realStandardGaussianNormalizer_positive.le _
  rw [Complex.norm_real, Real.norm_of_nonneg hZ]
  apply div_le_div_of_nonneg_right _ hZ
  calc
    _ <= MeasureTheory.integral gaussianTensorMeasure (fun x =>
        norm (standardGaussianPolynomialKernel (realGaussianEigenVariances M hM)
          (realGaussianAffinePolynomial M hM c) x)) :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (standardGaussianPolynomialKernel_affine_norm M hM c)

theorem stochasticGaussianAffinePolynomial_bound
    (T : Matrix Iota Iota Real) (q a rho : Real) (t : Complex)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hGap : 0 < 1 - norm t * rho) :
    norm (gaussianPolynomialState
        (realGaussianEigenVariances (bipartiteLift (centeredKernel T q))
          (bipartiteLift_hermitian (centeredKernel T q)))
        (realGaussianAffinePolynomial (bipartiteLift (centeredKernel T q))
          (bipartiteLift_hermitian (centeredKernel T q))
          (complexGaussianSquareRoot t))) <=
      Real.exp (2 * norm t / (1 - norm t * rho) *
        Real.sqrt ((Fintype.card Iota : Real) * (a - 1))) := by
  apply le_trans (realGaussianAffinePolynomial_state_norm_le _ _ _)
  exact stochasticGaussianAffineProductAverage_parameter_bound T q a rho t
    hq ha hRow hCol hNonneg hUpper hNorm hGap

end PrimeFactorOscillations
