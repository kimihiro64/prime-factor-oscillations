/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrection
import PrimeFactorOscillations.Helpers.HamiltonianMatrixSpectralAverage

/-! # Full resolvent spectral traces without deleting cross terms

The actual covariance is diagonalized by the original Hermitian eigenbasis.
Both the trace and the trace of its full matrix square are identified.
The latter includes every cross-block covariance product.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hermitian_resolvent_spectral_traces
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (hDen : forall i, Not (1 + hM.eigenvalues i = 0)) :
    IsUnit ((1 : Matrix Iota Iota Real) + M) /\
    Matrix.trace (resolventCovariance M) =
      Finset.sum Finset.univ (fun i => hM.eigenvalues i / (1 + hM.eigenvalues i)) /\
    Matrix.trace (resolventCovariance M * resolventCovariance M) =
      Finset.sum Finset.univ (fun i => (hM.eigenvalues i / (1 + hM.eigenvalues i)) ^ 2) := by
  let U := hM.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut Real (Matrix Iota Iota Real) U
  let lam := hM.eigenvalues
  let den := fun i => 1 + lam i
  let f := fun i => lam i / den i
  have hSpectral : M = F (Matrix.diagonal lam) := by
    simpa [F, U, lam] using hM.spectral_theorem
  have hUU : star (U : Matrix Iota Iota Real) * (U : Matrix Iota Iota Real) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_star_mul_self U
  have hTrace (A : Matrix Iota Iota Real) : Matrix.trace (F A) = Matrix.trace A := by
    change Matrix.trace (Unitary.conjStarAlgAut Real (Matrix Iota Iota Real) U A) = Matrix.trace A
    rw [Unitary.conjStarAlgAut_apply]
    calc
      _ = Matrix.trace ((star (U : Matrix Iota Iota Real) * (U : Matrix Iota Iota Real)) * A) := by
        rw [Matrix.trace_mul_comm, <- mul_assoc]
      _ = _ := by rw [hUU, one_mul]
  have hDiagonal : Matrix.diagonal den = (1 : Matrix Iota Iota Real) + Matrix.diagonal lam := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    case pos => subst j; simp [den, Matrix.diagonal_apply, Matrix.one_apply]
    case neg => simp [den, Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hH : (1 : Matrix Iota Iota Real) + M = F (Matrix.diagonal den) := by
    rw [hDiagonal, map_add, map_one, <- hSpectral]
  have hDiagInverse :
      Matrix.diagonal den * Matrix.diagonal (fun i => (den i) ^ (-1 : Int)) =
        (1 : Matrix Iota Iota Real) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    case pos =>
      subst j
      simp [Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply, den, lam, hDen]
    case neg =>
      simp [Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hHRight : ((1 : Matrix Iota Iota Real) + M) *
      F (Matrix.diagonal (fun i => (den i) ^ (-1 : Int))) = 1 := by
    rw [hH, <- map_mul, hDiagInverse, map_one]
  have hUnit : IsUnit ((1 : Matrix Iota Iota Real) + M) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse hHRight)
  have hDiagCov : Matrix.diagonal f * Matrix.diagonal den = Matrix.diagonal lam := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    case pos =>
      subst j
      simp [Matrix.mul_diagonal, Matrix.diagonal_apply, f, den, lam, hDen]
    case neg =>
      simp [Matrix.mul_diagonal, Matrix.diagonal_apply, hij]
  have hProduct : F (Matrix.diagonal f) * ((1 : Matrix Iota Iota Real) + M) = M := by
    rw [hH, <- map_mul, hDiagCov, <- hSpectral]
  have hCov : resolventCovariance M = F (Matrix.diagonal f) := by
    unfold resolventCovariance
    symm
    calc
      _ = (F (Matrix.diagonal f) * ((1 : Matrix Iota Iota Real) + M)) *
          Ring.inverse ((1 : Matrix Iota Iota Real) + M) := by
        rw [mul_assoc, Ring.mul_inverse_cancel _ hUnit, mul_one]
      _ = _ := by rw [hProduct]
  have hSquare : resolventCovariance M * resolventCovariance M =
      F (Matrix.diagonal (fun i => f i ^ 2)) := by
    rw [hCov, <- map_mul]
    congr 1
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    case pos =>
      subst j
      simp [Matrix.mul_diagonal, Matrix.diagonal_apply, pow_two]
    case neg =>
      simp [Matrix.mul_diagonal, Matrix.diagonal_apply, hij]
  refine And.intro hUnit (And.intro ?_ ?_)
  case refine_1 =>
    rw [hCov, hTrace]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_apply_eq, f, den, lam]
  case refine_2 =>
    rw [hSquare, hTrace]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_apply_eq, f, den, lam]

end PrimeFactorOscillations
