/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSignedRankOneComparison
import PrimeFactorOscillations.Helpers.HamiltonianWeightedSpectralReadout

/-! # Native eigenvalue outlier counts with multiplicities retained -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_real_eigenmatrix_column_gram
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (i j : Iota) :
    Finset.univ.sum (fun k =>
      realGaussianEigenMatrix M hM k i * realGaussianEigenMatrix M hM k j) =
        if i = j then (1 : Real) else 0 := by
  have h := congrArg (fun A : Matrix Iota Iota Real => A i j)
    (realGaussianEigenMatrix_orthogonal M hM)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

theorem hamiltonian_real_eigenmatrix_column_square_mass
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (i : Iota) :
    Finset.univ.sum (fun k => realGaussianEigenMatrix M hM k i ^ 2) = 1 := by
  simpa [pow_two] using hamiltonian_real_eigenmatrix_column_gram M hM i i

theorem hamiltonian_real_eigenmatrix_column_eigenvector
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (k i : Iota) :
    M.mulVec (fun j => realGaussianEigenMatrix M hM j k) i =
      hM.eigenvalues k * realGaussianEigenMatrix M hM i k := by
  have h := congrArg (fun A : Matrix Iota Iota Real => A i k)
    (hamiltonian_real_eigenmatrix_action M hM)
  rw [Matrix.mul_diagonal] at h
  exact h.trans (mul_comm _ _)

theorem hamiltonian_signed_rank_one_upper_eigenvalue_count
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (u v : Iota -> Real) (rho : Real)
    (hNorm : norm (M - hamiltonianSignedRankOneReference u v) <= rho) :
    (Finset.univ.filter (fun k => rho < hM.eigenvalues k)).card <= 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hXY := hamiltonian_real_eigenmatrix_column_gram M hM i j
  rw [if_neg hij] at hXY
  exact hamiltonian_signed_rank_one_no_two_upper_eigenvectors M u v
    (fun k => realGaussianEigenMatrix M hM k i)
    (fun k => realGaussianEigenMatrix M hM k j)
    rho (hM.eigenvalues i) (hM.eigenvalues j) hNorm
    (hamiltonian_real_eigenmatrix_column_square_mass M hM i)
    (hamiltonian_real_eigenmatrix_column_square_mass M hM j) hXY
    (hamiltonian_real_eigenmatrix_column_eigenvector M hM i)
    (hamiltonian_real_eigenmatrix_column_eigenvector M hM j)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem hamiltonian_signed_rank_one_lower_eigenvalue_count
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (u v : Iota -> Real) (rho : Real)
    (hNorm : norm (M - hamiltonianSignedRankOneReference u v) <= rho) :
    (Finset.univ.filter (fun k => hM.eigenvalues k < -rho)).card <= 1 := by
  classical
  have hSwap : -M - hamiltonianSignedRankOneReference v u =
      -(M - hamiltonianSignedRankOneReference u v) := by
    ext i j
    change -M i j - (v i * v j - u i * u j) =
      -(M i j - (u i * u j - v i * v j))
    ring
  have hNegativeNorm : norm (-M - hamiltonianSignedRankOneReference v u) <= rho := by
    rw [hSwap, norm_neg]
    exact hNorm
  have hNegEigen (k i : Iota) :
      (-M).mulVec (fun j => realGaussianEigenMatrix M hM j k) i =
        (-hM.eigenvalues k) * realGaussianEigenMatrix M hM i k := by
    change Finset.univ.sum (fun j => (-M i j) * realGaussianEigenMatrix M hM j k) =
      (-hM.eigenvalues k) * realGaussianEigenMatrix M hM i k
    simp only [neg_mul, Finset.sum_neg_distrib]
    change -(M.mulVec (fun j => realGaussianEigenMatrix M hM j k) i) =
      -(hM.eigenvalues k * realGaussianEigenMatrix M hM i k)
    rw [hamiltonian_real_eigenmatrix_column_eigenvector]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hXY := hamiltonian_real_eigenmatrix_column_gram M hM i j
  rw [if_neg hij] at hXY
  have hI : rho < -hM.eigenvalues i := by
    have h := (Finset.mem_filter.mp hi).2
    linarith only [h]
  have hJ : rho < -hM.eigenvalues j := by
    have h := (Finset.mem_filter.mp hj).2
    linarith only [h]
  exact hamiltonian_signed_rank_one_no_two_upper_eigenvectors (-M) v u
    (fun k => realGaussianEigenMatrix M hM k i)
    (fun k => realGaussianEigenMatrix M hM k j)
    rho (-hM.eigenvalues i) (-hM.eigenvalues j) hNegativeNorm
    (hamiltonian_real_eigenmatrix_column_square_mass M hM i)
    (hamiltonian_real_eigenmatrix_column_square_mass M hM j) hXY
    (hNegEigen i) (hNegEigen j) hI hJ

end PrimeFactorOscillations
