/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedGaussianGeometry

/-! # Exact compensated Gaussian integral for the signed rook polynomial

The actual integrable complex kernel is retained. Its covariance quotient,
standard Gaussian density, and nonzero tilted normalizer are explicit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianTilt_exponential_split (z : Complex) (x : Real) :
    Complex.exp (-gaussianTiltPrecision z * (x : Complex) ^ 2) =
      Complex.exp ((z / (1 + z)) * (x : Complex) ^ 2 / 2) *
        (Real.exp (-(1 / 2 : Real) * x ^ 2) : Complex) := by
  rw [Complex.ofReal_exp, <- Complex.exp_add]
  congr 1
  unfold gaussianTiltPrecision
  push_cast
  ring

theorem gaussianMvTiltKernel_reweight (z w : Iota -> Complex)
    (p : MvPolynomial Iota Complex) (x : Iota -> Real) :
    gaussianMvTiltKernel z w p x =
      MvPolynomial.eval (fun j => w j * (x j : Complex)) p *
        Complex.exp (Finset.sum Finset.univ
          (fun j => (z j / (1 + z j)) * (x j : Complex) ^ 2) / 2) *
        (realStandardGaussianDensity x : Complex) := by
  unfold gaussianMvTiltKernel
  simp_rw [gaussianTilt_exponential_split]
  rw [Finset.prod_mul_distrib, <- Complex.exp_sum, Finset.sum_div]
  unfold realStandardGaussianDensity
  push_cast
  ring

def realGaussianCompensatedKernel (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex) (x : Iota -> Real) : Complex :=
  Finset.prod Finset.univ (fun i => wickVertexFunction
      (realGaussianWeightedVector M hM (realGaussianQuotientWeights M hM s) x i)) *
    (realStandardGaussianDensity x : Complex)

def realGaussianCompensatedAverage (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex) : Complex :=
  MeasureTheory.integral gaussianTensorMeasure (realGaussianCompensatedKernel M hM s) /
    ((realStandardGaussianNormalizer ^ Fintype.card Iota : Real) : Complex)

theorem realGaussianCompensatedKernel_eq_tilt (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (x : Iota -> Real) :
    realGaussianCompensatedKernel M hM s x =
      gaussianMvTiltKernel (fun j => s * realGaussianEigenVariances M hM j)
        (realGaussianQuotientWeights M hM s)
        (realGaussianAffinePolynomial M hM 1) x := by
  rw [realGaussianCompensatedKernel,
    realGaussianQuotientVector_vertex_product M hM s hCol x,
    gaussianMvTiltKernel_reweight]
  rfl

theorem realGaussianCompensatedKernel_integrable (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (hDisk : forall j, norm (s * realGaussianEigenVariances M hM j) < 1) :
    MeasureTheory.Integrable (realGaussianCompensatedKernel M hM s)
      gaussianTensorMeasure := by
  have hEq : realGaussianCompensatedKernel M hM s =
      gaussianMvTiltKernel (fun j => s * realGaussianEigenVariances M hM j)
        (realGaussianQuotientWeights M hM s)
        (realGaussianAffinePolynomial M hM 1) :=
    funext (realGaussianCompensatedKernel_eq_tilt M hM s hCol)
  rw [hEq]
  exact gaussianMvTiltKernel_integrable _ _ hDisk _

theorem realGaussianCompensatedKernel_normalized (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (hDisk : forall j, norm (s * realGaussianEigenVariances M hM j) < 1) :
    MeasureTheory.integral gaussianTensorMeasure (realGaussianCompensatedKernel M hM s) /
        gaussianTensorTiltNormalizer (fun j => s * realGaussianEigenVariances M hM j) =
      gaussianPolynomialState (fun j => s * realGaussianEigenVariances M hM j)
        (realGaussianAffinePolynomial M hM 1) := by
  have hEq : realGaussianCompensatedKernel M hM s =
      gaussianMvTiltKernel (fun j => s * realGaussianEigenVariances M hM j)
        (realGaussianQuotientWeights M hM s)
        (realGaussianAffinePolynomial M hM 1) :=
    funext (realGaussianCompensatedKernel_eq_tilt M hM s hCol)
  rw [hEq]
  exact gaussianMvTiltKernel_normalized _ _ hDisk
    (realGaussianQuotientWeights_sq M hM s) _

theorem realGaussianCompensatedAverage_state (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (hDisk : forall j, norm (s * realGaussianEigenVariances M hM j) < 1) :
    gaussianPolynomialState (fun j => s * realGaussianEigenVariances M hM j)
        (realGaussianAffinePolynomial M hM 1) =
      (((realStandardGaussianNormalizer ^ Fintype.card Iota : Real) : Complex) /
        gaussianTensorTiltNormalizer (fun j => s * realGaussianEigenVariances M hM j)) *
          realGaussianCompensatedAverage M hM s := by
  have hZ : Not (((realStandardGaussianNormalizer ^ Fintype.card Iota : Real) :
      Complex) = 0) := by
    exact_mod_cast (pow_ne_zero (Fintype.card Iota)
      (ne_of_gt realStandardGaussianNormalizer_positive))
  rw [<- realGaussianCompensatedKernel_normalized M hM s hCol hDisk,
    realGaussianCompensatedAverage]
  field_simp

theorem realGaussianAffinePolynomial_scaled_rook {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (s : Complex) :
    gaussianPolynomialState
        (fun j => s * realGaussianEigenVariances (bipartiteLift B)
          (bipartiteLift_hermitian B) j)
        (realGaussianAffinePolynomial (bipartiteLift B)
          (bipartiteLift_hermitian B) 1) =
      hamiltonianComplexRookPolynomial B s := by
  let M := bipartiteLift B
  let hM := bipartiteLift_hermitian B
  let z := fun j => s * realGaussianEigenVariances M hM j
  let left := fun i : Fin n => realGaussianEigenRows M hM (Sum.inr i)
  let right := fun j : Fin n => realGaussianEigenRows M hM (Sum.inl j)
  have hCov : forall i j : Sum (Fin n) (Fin n),
      gaussianLinearCovariance z
          (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM j) =
        s * (M i j : Complex) := by
    intro i j
    exact realGaussianEigenCovariance_scaled M hM s i j
  have hLeft : forall i j, gaussianLinearCovariance z (left i) (left j) = 0 := by
    intro i j
    rw [hCov]
    change s * (0 : Complex) = 0
    ring
  have hRight : forall i j, gaussianLinearCovariance z (right i) (right j) = 0 := by
    intro i j
    rw [hCov]
    change s * (0 : Complex) = 0
    ring
  have hCross : forall i j,
      gaussianLinearCovariance z (left i) (right j) = s * (B j i : Complex) := by
    intro i j
    rw [hCov]
    rfl
  have hPoly : realGaussianAffinePolynomial M hM 1 =
      Finset.prod Finset.univ (fun i => 1 + gaussianLinearForm (left i)) *
        Finset.prod Finset.univ (fun j => 1 + gaussianLinearForm (right j)) := by
    unfold realGaussianAffinePolynomial
    rw [Fintype.prod_sum_type]
    dsimp only [left, right]
    simp only [map_one, one_mul]
    exact mul_comm _ _
  change gaussianPolynomialState z (realGaussianAffinePolynomial M hM 1) = _
  rw [hPoly, gaussianAffineProduct_rook z n left right hLeft hRight]
  unfold hamiltonianComplexRookPolynomial
  simp only [Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro sigma hs
  apply Finset.sum_congr rfl
  intro S hS
  simp_rw [hCross, Finset.prod_mul_distrib, Finset.prod_const]
  ring

theorem realGaussianCompensatedAverage_rook {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (s : Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => bipartiteLift B i j) = 0)
    (hDisk : forall j, norm (s * realGaussianEigenVariances (bipartiteLift B)
      (bipartiteLift_hermitian B) j) < 1) :
    hamiltonianComplexRookPolynomial B s =
      (((realStandardGaussianNormalizer ^ Fintype.card (Sum (Fin n) (Fin n)) : Real) :
        Complex) /
        gaussianTensorTiltNormalizer (fun j => s *
          realGaussianEigenVariances (bipartiteLift B) (bipartiteLift_hermitian B) j)) *
      realGaussianCompensatedAverage (bipartiteLift B) (bipartiteLift_hermitian B) s := by
  rw [<- realGaussianAffinePolynomial_scaled_rook]
  exact realGaussianCompensatedAverage_state _ _ s hCol hDisk

end PrimeFactorOscillations
