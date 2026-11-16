/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianWeightedBipartiteModes

/-! # Independent native eigenvalue readout from the complete weighted-mode error -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_weighted_eigenvalue_error_readout
    (S : Matrix Iota Iota Real) (u v : Iota -> Real) (R rho lambda : Real)
    (x : Sum Iota Iota -> Real)
    (hLeft : forall i, Finset.univ.sum (fun j => S i j * v j) = u i)
    (hRight : forall j, Finset.univ.sum (fun i => S i j * u i) = v j)
    (hX : Exists (fun i => Not (x i = 0)))
    (hEigen : forall i, (bipartiteLift S).mulVec x i = lambda * x i)
    (hOne : Not (lambda = 1)) (hMinus : Not (lambda = -(1 : Real)))
    (hNorm : norm (S - hamiltonianWeightedCrossMode u v R) <= rho) :
    abs lambda <= rho := by
  have hSums := hamiltonian_weighted_eigenvector_sums S u v hLeft hRight
    x lambda hEigen hOne hMinus
  let P := bipartiteLift (hamiltonianWeightedCrossMode u v R)
  have hReference (i : Sum Iota Iota) : P.mulVec x i = 0 := by
    cases i with
    | inl i =>
      rw [hamiltonian_weighted_mode_left, hSums.2, mul_zero]
    | inr j =>
      rw [hamiltonian_weighted_mode_right, hSums.1, mul_zero]
  have hDiff : bipartiteLift S - P =
      bipartiteLift (S - hamiltonianWeightedCrossMode u v R) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [P, bipartiteLift, Matrix.fromBlocks, Matrix.transpose, Matrix.sub_apply]
  have hFull : norm (bipartiteLift S - P) <= rho := by
    rw [hDiff, hamiltonian_bipartite_lift_norm]
    exact hNorm
  exact hamiltonian_eigenvalue_error_bound (bipartiteLift S) P x lambda rho
    hX hEigen hReference hFull

theorem hamiltonian_real_eigenmatrix_column_nonzero
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (k : Iota) :
    Exists (fun i => Not (realGaussianEigenMatrix M hM i k = 0)) := by
  classical
  let U := realGaussianEigenMatrix M hM
  by_contra hNone
  have hZero (i : Iota) : U i k = 0 := by
    by_contra hi
    exact hNone (Exists.intro i hi)
  have h := congrArg (fun A : Matrix Iota Iota Real => A k k)
    (realGaussianEigenMatrix_orthogonal M hM)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, ite_true] at h
  change Finset.univ.sum (fun i => U i k * U i k) = 1 at h
  simp only [hZero, mul_zero, Finset.sum_const_zero] at h
  norm_num at h

theorem hamiltonian_weighted_native_eigenvalue_readout
    (S : Matrix Iota Iota Real) (u v : Iota -> Real) (R rho : Real)
    (hLeft : forall i, Finset.univ.sum (fun j => S i j * v j) = u i)
    (hRight : forall j, Finset.univ.sum (fun i => S i j * u i) = v j)
    (hNorm : norm (S - hamiltonianWeightedCrossMode u v R) <= rho)
    (k : Sum Iota Iota)
    (hOne : Not ((bipartiteLift_hermitian S).eigenvalues k = 1))
    (hMinus : Not ((bipartiteLift_hermitian S).eigenvalues k = -(1 : Real))) :
    abs ((bipartiteLift_hermitian S).eigenvalues k) <= rho := by
  let M := bipartiteLift S
  let hM := bipartiteLift_hermitian S
  let U := realGaussianEigenMatrix M hM
  let lambda := hM.eigenvalues k
  have hEigen (i : Sum Iota Iota) :
      M.mulVec (fun j => U j k) i = lambda * U i k := by
    have h := congrArg
      (fun A : Matrix (Sum Iota Iota) (Sum Iota Iota) Real => A i k)
      (hamiltonian_real_eigenmatrix_action M hM)
    change (M * U) i k = (U * Matrix.diagonal hM.eigenvalues) i k at h
    rw [Matrix.mul_diagonal] at h
    exact h.trans (mul_comm _ _)
  exact hamiltonian_weighted_eigenvalue_error_readout S u v R rho lambda
    (fun i => U i k) hLeft hRight
    (hamiltonian_real_eigenmatrix_column_nonzero M hM k) hEigen hOne hMinus hNorm

end PrimeFactorOscillations
