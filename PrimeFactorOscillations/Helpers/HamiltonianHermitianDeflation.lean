/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCenteredContraction
import PrimeFactorOscillations.Helpers.HamiltonianGaussianSpectralRealization

/-! # Native Hermitian readout after exact signed exceptional-mode subtraction -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_real_orthogonal_norm_le_one
    (U : Matrix Iota Iota Real) (hOrth : U.transpose * U = 1) :
    norm U <= 1 := by
  have hStar : U.conjTranspose = U.transpose := by ext i j; rfl
  have hGram := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [hStar, hOrth] at hGram
  have hOne := hamiltonian_real_projection_norm (1 : Matrix Iota Iota Real)
    Matrix.transpose_one (one_mul _)
  nlinarith only [hGram, hOne, norm_nonneg U]

theorem hamiltonian_orthogonal_diagonal_action_norm
    (A U : Matrix Iota Iota Real) (mu : Iota -> Real) (rho : Real)
    (hp : 0 <= rho) (hLeft : U.transpose * U = 1) (hRight : U * U.transpose = 1)
    (hAction : forall i k, (A * U) i k = U i k * mu k)
    (hMu : forall k, abs (mu k) <= rho) :
    norm A <= rho := by
  have hAU : A * U = U * Matrix.diagonal mu := by
    ext i k
    simpa only [Matrix.mul_diagonal] using hAction i k
  have hA : A = (U * Matrix.diagonal mu) * U.transpose := by
    rw [<- hAU, Matrix.mul_assoc, hRight, Matrix.mul_one]
  have hU := hamiltonian_real_orthogonal_norm_le_one U hLeft
  have hUt : norm U.transpose <= 1 := by
    rw [hamiltonian_real_transpose_norm]
    exact hU
  have hD : norm (Matrix.diagonal mu) <= rho := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hp).mpr (fun k => by
      simpa only [Real.norm_eq_abs] using hMu k)
  rw [hA]
  calc
    _ <= norm (U * Matrix.diagonal mu) * norm U.transpose := Matrix.l2_opNorm_mul _ _
    _ <= (norm U * norm (Matrix.diagonal mu)) * norm U.transpose :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ <= (1 * rho) * 1 := mul_le_mul
      (mul_le_mul hU hD (norm_nonneg _) (by norm_num)) hUt
      (norm_nonneg _) (by simpa only [one_mul] using hp)
    _ = rho := by ring

theorem hamiltonian_real_eigenmatrix_right_inverse
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) :
    realGaussianEigenMatrix M hM * (realGaussianEigenMatrix M hM).transpose = 1 := by
  let U := realGaussianEigenMatrix M hM
  have hStar : star U = U.transpose := by ext i j; rfl
  have hUnit :
      (hM.eigenvectorUnitary : Matrix Iota Iota Real) *
        star (hM.eigenvectorUnitary : Matrix Iota Iota Real) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self hM.eigenvectorUnitary
  change U * star U = 1 at hUnit
  rw [hStar] at hUnit
  exact hUnit

theorem hamiltonian_real_eigenmatrix_action
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) :
    M * realGaussianEigenMatrix M hM =
      realGaussianEigenMatrix M hM * Matrix.diagonal hM.eigenvalues := by
  let U := realGaussianEigenMatrix M hM
  calc
    M * U = ((U * Matrix.diagonal hM.eigenvalues) * U.transpose) * U :=
      congrArg (fun A : Matrix Iota Iota Real => A * U)
        (realGaussianEigenMatrix_decomposition M hM)
    _ = U * Matrix.diagonal hM.eigenvalues := by
      rw [Matrix.mul_assoc, realGaussianEigenMatrix_orthogonal M hM, Matrix.mul_one]

theorem hamiltonian_hermitian_signed_deflation_norm
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (P : Matrix Iota Iota Real) (rho : Real) (hp : 0 <= rho)
    (hSpectrum : forall k, Not (hM.eigenvalues k = 1) ->
      Not (hM.eigenvalues k = -(1 : Real)) -> abs (hM.eigenvalues k) <= rho)
    (hExceptional : forall k,
      Or (hM.eigenvalues k = 1) (hM.eigenvalues k = -(1 : Real)) ->
      forall i, (P * realGaussianEigenMatrix M hM) i k =
        realGaussianEigenMatrix M hM i k * hM.eigenvalues k)
    (hOther : forall k, Not (hM.eigenvalues k = 1) ->
      Not (hM.eigenvalues k = -(1 : Real)) ->
      forall i, (P * realGaussianEigenMatrix M hM) i k = 0) :
    norm (M - P) <= rho := by
  classical
  let U := realGaussianEigenMatrix M hM
  let mu := fun k => if Or (hM.eigenvalues k = 1)
    (hM.eigenvalues k = -(1 : Real)) then (0 : Real) else hM.eigenvalues k
  have hAction (i k : Iota) : ((M - P) * U) i k = U i k * mu k := by
    rw [sub_mul, Matrix.sub_apply, hamiltonian_real_eigenmatrix_action M hM,
      Matrix.mul_diagonal]
    by_cases he : Or (hM.eigenvalues k = 1) (hM.eigenvalues k = -(1 : Real))
    case pos =>
      rw [hExceptional k he i]
      simp only [mu, U, if_pos he, mul_zero, sub_self]
    case neg =>
      have hp1 : Not (hM.eigenvalues k = 1) := fun h => he (Or.inl h)
      have hpm : Not (hM.eigenvalues k = -(1 : Real)) := fun h => he (Or.inr h)
      rw [hOther k hp1 hpm i]
      simp only [mu, U, if_neg he, sub_zero]
  apply hamiltonian_orthogonal_diagonal_action_norm (M - P) U mu rho hp
    (realGaussianEigenMatrix_orthogonal M hM) (hamiltonian_real_eigenmatrix_right_inverse M hM)
    hAction
  intro k
  by_cases he : Or (hM.eigenvalues k = 1) (hM.eigenvalues k = -(1 : Real))
  case pos => simpa only [mu, U, if_pos he, abs_zero] using hp
  case neg =>
    simp only [mu, U, if_neg he]
    exact hSpectrum k (fun h => he (Or.inl h)) (fun h => he (Or.inr h))

end PrimeFactorOscillations
