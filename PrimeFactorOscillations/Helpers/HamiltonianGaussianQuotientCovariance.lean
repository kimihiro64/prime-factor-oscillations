/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedGaussianNormalizer

/-! # The actual spectral quotient covariance equals the full resolvent

All conjugations, inverse factors, and repeated-coordinate covariances
are exact. The generic diagonal argument applies to real or complex fields.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def orthogonalMatrixConjugate {K : Type*} [CommRing K]
    (U A : Matrix Iota Iota K) : Matrix Iota Iota K := U * A * U.transpose

theorem orthogonalMatrixConjugate_one {K : Type*} [CommRing K]
    (U : Matrix Iota Iota K) (hReverse : U * U.transpose = 1) :
    orthogonalMatrixConjugate U 1 = 1 := by
  simp only [orthogonalMatrixConjugate, Matrix.mul_one, hReverse]

theorem orthogonalMatrixConjugate_add {K : Type*} [CommRing K]
    (U A B : Matrix Iota Iota K) :
    orthogonalMatrixConjugate U (A + B) =
      orthogonalMatrixConjugate U A + orthogonalMatrixConjugate U B := by
  simp only [orthogonalMatrixConjugate, Matrix.mul_add, Matrix.add_mul]

theorem orthogonalMatrixConjugate_smul {K : Type*} [CommRing K]
    (U A : Matrix Iota Iota K) (c : K) :
    orthogonalMatrixConjugate U (HSMul.hSMul c A) =
      HSMul.hSMul c (orthogonalMatrixConjugate U A) := by
  simp only [orthogonalMatrixConjugate, Matrix.mul_smul, Matrix.smul_mul]

theorem orthogonalMatrixConjugate_mul {K : Type*} [CommRing K]
    (U A B : Matrix Iota Iota K) (hOrth : U.transpose * U = 1) :
    orthogonalMatrixConjugate U A * orthogonalMatrixConjugate U B =
      orthogonalMatrixConjugate U (A * B) := by
  unfold orthogonalMatrixConjugate
  calc
    _ = (U * A) * (U.transpose * U) * (B * U.transpose) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hOrth, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem orthogonalMatrixConjugate_diagonal_unit {K : Type*} [Field K]
    (U : Matrix Iota Iota K) (hOrth : U.transpose * U = 1)
    (hReverse : U * U.transpose = 1)
    (d : Iota -> K) (hD : forall i, Not (d i = 0)) :
    Ring.inverse (orthogonalMatrixConjugate U (Matrix.diagonal d)) =
      orthogonalMatrixConjugate U (Matrix.diagonal (fun i => 1 / d i)) := by
  let v : Units (Matrix Iota Iota K) :=
    { val := orthogonalMatrixConjugate U (Matrix.diagonal d)
      inv := orthogonalMatrixConjugate U (Matrix.diagonal (fun i => 1 / d i))
      val_inv := by
        rw [orthogonalMatrixConjugate_mul U _ _ hOrth, Matrix.diagonal_mul_diagonal]
        have hOne : Matrix.diagonal (fun i => d i * (1 / d i)) =
            (1 : Matrix Iota Iota K) := by
          ext i j
          by_cases hEq : i = j
          case pos => subst j; simp [hD i]
          case neg => simp [Matrix.diagonal_apply, Matrix.one_apply, hEq]
        rw [hOne, orthogonalMatrixConjugate_one U hReverse]
      inv_val := by
        rw [orthogonalMatrixConjugate_mul U _ _ hOrth, Matrix.diagonal_mul_diagonal]
        have hOne : Matrix.diagonal (fun i => (1 / d i) * d i) =
            (1 : Matrix Iota Iota K) := by
          ext i j
          by_cases hEq : i = j
          case pos => subst j; simp [hD i]
          case neg => simp [Matrix.diagonal_apply, Matrix.one_apply, hEq]
        rw [hOne, orthogonalMatrixConjugate_one U hReverse] }
  change Ring.inverse (v : Matrix Iota Iota K) = ((Inv.inv v : Units _) : Matrix Iota Iota K)
  exact Ring.inverse_unit v

theorem orthogonalQuotientMatrix_resolvent {K : Type*} [Field K]
    (U : Matrix Iota Iota K) (hOrth : U.transpose * U = 1)
    (hReverse : U * U.transpose = 1)
    (a : Iota -> K) (hAdd : forall i, Not (1 + a i = 0)) :
    orthogonalMatrixConjugate U (Matrix.diagonal (fun i => a i / (1 + a i))) =
      orthogonalMatrixConjugate U (Matrix.diagonal a) *
        Ring.inverse (1 + orthogonalMatrixConjugate U (Matrix.diagonal a)) := by
  have hDiag : Matrix.diagonal (fun i => 1 + a i) =
      (1 : Matrix Iota Iota K) + Matrix.diagonal a := by
    ext i j
    by_cases hEq : i = j
    case pos => subst j; simp
    case neg => simp [Matrix.diagonal_apply, Matrix.one_apply, hEq]
  have hSum : 1 + orthogonalMatrixConjugate U (Matrix.diagonal a) =
      orthogonalMatrixConjugate U (Matrix.diagonal (fun i => 1 + a i)) := by
    rw [hDiag, orthogonalMatrixConjugate_add, orthogonalMatrixConjugate_one U hReverse]
  rw [hSum, orthogonalMatrixConjugate_diagonal_unit U hOrth hReverse _ hAdd,
    orthogonalMatrixConjugate_mul U _ _ hOrth, Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  ring

theorem realGaussianEigenMatrix_reverse_orthogonal (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) :
    realGaussianEigenMatrix M hM * (realGaussianEigenMatrix M hM).transpose = 1 := by
  have hUnit : (hM.eigenvectorUnitary : Matrix Iota Iota Real) *
      star (hM.eigenvectorUnitary : Matrix Iota Iota Real) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hStar : star (realGaussianEigenMatrix M hM) =
      (realGaussianEigenMatrix M hM).transpose := by
    ext i j
    rfl
  change realGaussianEigenMatrix M hM * star (realGaussianEigenMatrix M hM) = 1 at hUnit
  rw [hStar] at hUnit
  exact hUnit

def realGaussianQuotientCovariance (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real) : Matrix Iota Iota Real :=
  orthogonalMatrixConjugate (realGaussianEigenMatrix M hM)
    (Matrix.diagonal (fun j => s * hM.eigenvalues j / (1 + s * hM.eigenvalues j)))

theorem realGaussianQuotientCovariance_resolvent (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real)
    (hAdd : forall j, Not (1 + s * hM.eigenvalues j = 0)) :
    realGaussianQuotientCovariance M hM s =
      resolventCovariance (HSMul.hSMul s M) := by
  have hQ : orthogonalMatrixConjugate (realGaussianEigenMatrix M hM)
      (Matrix.diagonal (fun j => s * hM.eigenvalues j)) = HSMul.hSMul s M := by
    have hDiag : Matrix.diagonal (fun j => s * hM.eigenvalues j) =
        HSMul.hSMul s (Matrix.diagonal hM.eigenvalues) := by
      ext i j
      by_cases hEq : i = j
      case pos => subst j; simp
      case neg => simp [Matrix.diagonal_apply, Matrix.smul_apply, hEq]
    rw [hDiag, orthogonalMatrixConjugate_smul]
    exact congrArg (fun A : Matrix Iota Iota Real => HSMul.hSMul s A)
      (realGaussianEigenMatrix_decomposition M hM).symm
  unfold realGaussianQuotientCovariance
  rw [orthogonalQuotientMatrix_resolvent _ (realGaussianEigenMatrix_orthogonal M hM)
    (realGaussianEigenMatrix_reverse_orthogonal M hM) _ hAdd, hQ]
  rfl

theorem realGaussianQuotientCovariance_entry (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real) (i k : Iota) :
    gaussianLinearCovariance
        (fun j => (s : Complex) * realGaussianEigenVariances M hM j /
          (1 + (s : Complex) * realGaussianEigenVariances M hM j))
        (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM k) =
      (realGaussianQuotientCovariance M hM s i k : Complex) := by
  have hReal : Finset.sum Finset.univ (fun j =>
      (s * hM.eigenvalues j / (1 + s * hM.eigenvalues j)) *
        realGaussianEigenMatrix M hM i j * realGaussianEigenMatrix M hM k j) =
      realGaussianQuotientCovariance M hM s i k := by
    unfold realGaussianQuotientCovariance orthogonalMatrixConjugate
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold gaussianLinearCovariance realGaussianEigenVariances realGaussianEigenRows
  have hComplex := congrArg Complex.ofReal hReal
  push_cast at hComplex
  exact hComplex

theorem realGaussianQuotientCovariance_entry_resolvent (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real)
    (hAdd : forall j, Not (1 + s * hM.eigenvalues j = 0)) (i k : Iota) :
    gaussianLinearCovariance
        (fun j => (s : Complex) * realGaussianEigenVariances M hM j /
          (1 + (s : Complex) * realGaussianEigenVariances M hM j))
        (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM k) =
      (resolventCovariance (HSMul.hSMul s M) i k : Complex) := by
  rw [realGaussianQuotientCovariance_entry,
    realGaussianQuotientCovariance_resolvent M hM s hAdd]

end PrimeFactorOscillations
