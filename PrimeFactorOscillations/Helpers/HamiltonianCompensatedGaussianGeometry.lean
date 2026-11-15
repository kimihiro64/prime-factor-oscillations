/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRookGammaTail
import PrimeFactorOscillations.Helpers.HamiltonianWickVertex

/-! # Signed complex geometry of the actual compensated Gaussian vector

Bilinear squares retain their complex signs. Orthogonality cancels every
cross term before the compensated vertex product is reweighted.
Quotient weights preserve the full zero-sum constraint.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem commutativeOrthogonal_square_sum {R : Type*} [CommSemiring R]
    (U : Matrix Iota Iota R) (hOrth : U.transpose * U = 1) (f : Iota -> R) :
    Finset.sum Finset.univ (fun i => (U.mulVec f i) ^ 2) =
      Finset.sum Finset.univ (fun i => f i ^ 2) := by
  have hAdj : Matrix.vecMul (U.mulVec f) U = f := by
    calc
      Matrix.vecMul (U.mulVec f) U = U.transpose.mulVec (U.mulVec f) := by
        ext j
        simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (U.transpose * U).mulVec f := Matrix.mulVec_mulVec f U.transpose U
      _ = f := by rw [hOrth, Matrix.one_mulVec]
  have hDot := Matrix.dotProduct_mulVec (U.mulVec f) U f
  rw [hAdj] at hDot
  simpa only [dotProduct, <- pow_two] using hDot

theorem realOrthogonal_complex_bilinear_square (U : Matrix Iota Iota Real)
    (hOrth : U.transpose * U = 1) (f : Iota -> Complex) :
    Finset.sum Finset.univ
        (fun i => (Finset.sum Finset.univ (fun j => (U i j : Complex) * f j)) ^ 2) =
      Finset.sum Finset.univ (fun i => f i ^ 2) := by
  let V : Matrix Iota Iota Complex := fun i j => (U i j : Complex)
  have hV : V.transpose * V = 1 := by
    ext i j
    have h := congrArg (fun A : Matrix Iota Iota Real => A i j) hOrth
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    change Finset.sum Finset.univ (fun k => (U k i : Complex) * (U k j : Complex)) =
      (if i = j then (1 : Complex) else 0)
    have hComplex := congrArg Complex.ofReal h
    push_cast at hComplex
    by_cases hEq : i = j
    all_goals simpa only [hEq, ite_true, ite_false, Complex.ofReal_one,
      Complex.ofReal_zero] using hComplex
  exact commutativeOrthogonal_square_sum V hV f

def realGaussianWeightedVector (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (w : Iota -> Complex) (x : Iota -> Real) (i : Iota) : Complex :=
  Finset.sum Finset.univ (fun j =>
    (realGaussianEigenMatrix M hM i j : Complex) * (w j * (x j : Complex)))

theorem realGaussianWeightedVector_zero_sum (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (w : Iota -> Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (hW : forall j, hM.eigenvalues j = 0 -> w j = 0) (x : Iota -> Real) :
    Finset.sum Finset.univ (realGaussianWeightedVector M hM w x) = 0 := by
  unfold realGaussianWeightedVector
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  rw [<- Finset.sum_mul]
  by_cases hLambda : hM.eigenvalues j = 0
  case pos => rw [hW j hLambda, zero_mul, mul_zero]
  case neg =>
    have hBalance := realGaussianEigenColumn_balance M hM hCol j
    have hReal : Finset.sum Finset.univ
        (fun i => realGaussianEigenMatrix M hM i j) = 0 :=
      (mul_eq_zero.mp hBalance).resolve_left hLambda
    have hComplex : Finset.sum Finset.univ
        (fun i => (realGaussianEigenMatrix M hM i j : Complex)) = 0 := by
      exact_mod_cast hReal
    rw [hComplex, zero_mul]

theorem realGaussianWeightedVector_square_sum (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (w : Iota -> Complex) (x : Iota -> Real) :
    Finset.sum Finset.univ (fun i => realGaussianWeightedVector M hM w x i ^ 2) =
      Finset.sum Finset.univ (fun j => w j ^ 2 * (x j : Complex) ^ 2) := by
  calc
    _ = Finset.sum Finset.univ (fun j => (w j * (x j : Complex)) ^ 2) :=
      realOrthogonal_complex_bilinear_square (realGaussianEigenMatrix M hM)
        (realGaussianEigenMatrix_orthogonal M hM) (fun j => w j * (x j : Complex))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_pow]

theorem realGaussianAffinePolynomial_eval_weighted (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (w : Iota -> Complex) (x : Iota -> Real) :
    MvPolynomial.eval (fun j => w j * (x j : Complex))
        (realGaussianAffinePolynomial M hM 1) =
      Finset.prod Finset.univ (fun i =>
        1 + realGaussianWeightedVector M hM w x i) := by
  simp only [realGaussianAffinePolynomial, map_prod, map_add, map_one, map_mul,
    MvPolynomial.eval_C, one_mul, gaussianLinearForm, map_sum, MvPolynomial.eval_X]
  rfl

theorem wickVertexFunction_product_zero_sum (Y : Iota -> Complex)
    (hZero : Finset.sum Finset.univ Y = 0) :
    Finset.prod Finset.univ (fun i => wickVertexFunction (Y i)) =
      Finset.prod Finset.univ (fun i => 1 + Y i) *
        Complex.exp (Finset.sum Finset.univ (fun i => Y i ^ 2) / 2) := by
  unfold wickVertexFunction
  rw [Finset.prod_mul_distrib, <- Complex.exp_sum]
  have hExponent :
      Finset.sum Finset.univ (fun i => -Y i + Y i ^ 2 / 2) =
        Finset.sum Finset.univ (fun i => Y i ^ 2) / 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hZero,
      Finset.sum_div, neg_zero, zero_add]
  rw [hExponent]

theorem realGaussianWeightedVector_vertex_product (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (w : Iota -> Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (hW : forall j, hM.eigenvalues j = 0 -> w j = 0) (x : Iota -> Real) :
    Finset.prod Finset.univ (fun i =>
        wickVertexFunction (realGaussianWeightedVector M hM w x i)) =
      MvPolynomial.eval (fun j => w j * (x j : Complex))
          (realGaussianAffinePolynomial M hM 1) *
        Complex.exp (Finset.sum Finset.univ
          (fun j => w j ^ 2 * (x j : Complex) ^ 2) / 2) := by
  rw [wickVertexFunction_product_zero_sum _
    (realGaussianWeightedVector_zero_sum M hM w hCol hW x),
    realGaussianWeightedVector_square_sum, realGaussianAffinePolynomial_eval_weighted]

def realGaussianQuotientWeights (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex) (j : Iota) : Complex :=
  complexGaussianSquareRoot
    (s * (hM.eigenvalues j : Complex) / (1 + s * (hM.eigenvalues j : Complex)))

theorem realGaussianQuotientWeights_sq (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex) (j : Iota) :
    realGaussianQuotientWeights M hM s j ^ 2 =
      s * (hM.eigenvalues j : Complex) / (1 + s * (hM.eigenvalues j : Complex)) :=
  complexGaussianSquareRoot_sq _

theorem realGaussianQuotientWeights_zero (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex) (j : Iota) (h : hM.eigenvalues j = 0) :
    realGaussianQuotientWeights M hM s j = 0 := by
  have hSq := realGaussianQuotientWeights_sq M hM s j
  rw [h, Complex.ofReal_zero, mul_zero, zero_div] at hSq
  have hMul : realGaussianQuotientWeights M hM s j *
      realGaussianQuotientWeights M hM s j = 0 := by
    simpa only [pow_two] using hSq
  exact (mul_eq_zero.mp hMul).elim id id

theorem realGaussianQuotientVector_zero_sum (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (x : Iota -> Real) :
    Finset.sum Finset.univ
      (realGaussianWeightedVector M hM (realGaussianQuotientWeights M hM s) x) = 0 :=
  realGaussianWeightedVector_zero_sum M hM _ hCol
    (realGaussianQuotientWeights_zero M hM s) x

theorem realGaussianQuotientVector_vertex_product (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (x : Iota -> Real) :
    Finset.prod Finset.univ (fun i => wickVertexFunction
        (realGaussianWeightedVector M hM (realGaussianQuotientWeights M hM s) x i)) =
      MvPolynomial.eval (fun j => realGaussianQuotientWeights M hM s j * (x j : Complex))
          (realGaussianAffinePolynomial M hM 1) *
        Complex.exp (Finset.sum Finset.univ (fun j =>
          (s * (hM.eigenvalues j : Complex) / (1 + s * (hM.eigenvalues j : Complex))) *
            (x j : Complex) ^ 2) / 2) := by
  rw [realGaussianWeightedVector_vertex_product M hM _ hCol
    (realGaussianQuotientWeights_zero M hM s) x]
  simp_rw [realGaussianQuotientWeights_sq]

end PrimeFactorOscillations
