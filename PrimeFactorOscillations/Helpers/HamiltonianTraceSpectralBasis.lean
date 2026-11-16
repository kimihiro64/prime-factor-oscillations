/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFiniteFactorTrace
import PrimeFactorOscillations.Helpers.HamiltonianHermitianDeflation

/-! # Exact spectral trace powers and every ordered mixed return pair -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_spectral_conjugation_trace
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian) (Y : Matrix Iota Iota Real) :
    Matrix.trace (Unitary.conjStarAlgAut Real (Matrix Iota Iota Real)
      hA.eigenvectorUnitary Y) = Matrix.trace Y := by
  let U := realGaussianEigenMatrix A hA
  rw [Unitary.conjStarAlgAut_apply]
  change Matrix.trace (U * Y * star U) = Matrix.trace Y
  have hUnit : star U * U = 1 := by
    simpa only [U, realGaussianEigenMatrix, Unitary.coe_star] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [Matrix.trace_mul_cycle, hUnit, Matrix.one_mul]

theorem hamiltonian_hermitian_trace_power
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian) (p : Nat) :
    Matrix.trace (A ^ p) = Finset.univ.sum (fun i => hA.eigenvalues i ^ p) := by
  let phi := Unitary.conjStarAlgAut Real (Matrix Iota Iota Real) hA.eigenvectorUnitary
  have hSpec : A = phi (Matrix.diagonal hA.eigenvalues) := by
    simpa [phi] using hA.spectral_theorem
  calc
    _ = Matrix.trace (phi (Matrix.diagonal hA.eigenvalues) ^ p) :=
      congrArg (fun M : Matrix Iota Iota Real => Matrix.trace (M ^ p)) hSpec
    _ = Matrix.trace (phi ((Matrix.diagonal hA.eigenvalues) ^ p)) := by rw [map_pow]
    _ = Matrix.trace ((Matrix.diagonal hA.eigenvalues) ^ p) :=
      hamiltonian_spectral_conjugation_trace A hA _
    _ = _ := by simp only [Matrix.diagonal_pow, Matrix.trace_diagonal, Pi.pow_apply]

def hamiltonianSpectralConjugate (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (X : Matrix Iota Iota Real) : Matrix Iota Iota Real :=
  star (realGaussianEigenMatrix A hA) * X * realGaussianEigenMatrix A hA

theorem hamiltonian_spectral_conjugate_inverse
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian) (X : Matrix Iota Iota Real) :
    Unitary.conjStarAlgAut Real (Matrix Iota Iota Real) hA.eigenvectorUnitary
      (hamiltonianSpectralConjugate A hA X) = X := by
  let U := realGaussianEigenMatrix A hA
  have hRight : U * star U = 1 := by
    simpa only [U, realGaussianEigenMatrix, Unitary.coe_star] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply]
  change U * (star U * X * U) * star U = X
  calc
    _ = (U * star U) * X * (U * star U) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hRight, Matrix.one_mul, Matrix.mul_one]

theorem hamiltonian_spectral_conjugate_norm
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian) (X : Matrix Iota Iota Real) :
    norm (hamiltonianSpectralConjugate A hA X) <= norm X := by
  let U := realGaussianEigenMatrix A hA
  have hU : norm U <= 1 :=
    hamiltonian_real_orthogonal_norm_le_one U (realGaussianEigenMatrix_orthogonal A hA)
  have hStarNorm : norm (star U) = norm U := Matrix.l2_opNorm_conjTranspose U
  calc
    _ <= norm (star U * X) * norm U := Matrix.l2_opNorm_mul _ _
    _ <= (norm (star U) * norm X) * norm U :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ <= (1 * norm X) * 1 :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right (hStarNorm.le.trans hU) (norm_nonneg _))
        hU (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem hamiltonian_spectral_conjugate_hermitian
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (X : Matrix Iota Iota Real) (hX : X.IsHermitian) :
    (hamiltonianSpectralConjugate A hA X).IsHermitian := by
  change star X = X at hX
  change star (hamiltonianSpectralConjugate A hA X) = hamiltonianSpectralConjugate A hA X
  unfold hamiltonianSpectralConjugate
  simp only [star_mul, star_star, hX, Matrix.mul_assoc]

theorem hamiltonian_hermitian_mixed_trace_pairs
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (X : Matrix Iota Iota Real) (hX : X.IsHermitian) (a b : Nat) :
    Matrix.trace (A ^ a * X * A ^ b * X) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun k =>
        hamiltonianSpectralConjugate A hA X i k ^ 2 *
          hA.eigenvalues i ^ a * hA.eigenvalues k ^ b)) := by
  let phi := Unitary.conjStarAlgAut Real (Matrix Iota Iota Real) hA.eigenvectorUnitary
  let D := Matrix.diagonal hA.eigenvalues
  let B := hamiltonianSpectralConjugate A hA X
  have hPhiD : phi D = A := by simpa [phi, D] using hA.spectral_theorem.symm
  have hPhiB : phi B = X := hamiltonian_spectral_conjugate_inverse A hA X
  have hB : B.IsHermitian := hamiltonian_spectral_conjugate_hermitian A hA X hX
  have hSym (i k : Iota) : B k i = B i k := by
    change B.conjTranspose = B at hB
    have h := congrArg (fun M : Matrix Iota Iota Real => M i k) hB
    change B k i = B i k at h
    exact h
  have hMap : phi (D ^ a * B * D ^ b * B) = A ^ a * X * A ^ b * X := by
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, hPhiD, hPhiB]
  have hEntry (i k : Iota) :
      (D ^ a * B * D ^ b) i k =
        hA.eigenvalues i ^ a * B i k * hA.eigenvalues k ^ b := by
    simp only [D, Matrix.diagonal_pow, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.pow_apply]
  calc
    _ = Matrix.trace (phi (D ^ a * B * D ^ b * B)) := congrArg Matrix.trace hMap.symm
    _ = Matrix.trace (D ^ a * B * D ^ b * B) :=
      hamiltonian_spectral_conjugation_trace A hA _
    _ = _ := by
      change Finset.univ.sum (fun i => Finset.univ.sum
        (fun k => (D ^ a * B * D ^ b) i k * B k i)) = _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [hEntry, hSym i k]
      change (hA.eigenvalues i ^ a * B i k * hA.eigenvalues k ^ b) * B i k =
        B i k ^ 2 * hA.eigenvalues i ^ a * hA.eigenvalues k ^ b
      ring

end PrimeFactorOscillations
