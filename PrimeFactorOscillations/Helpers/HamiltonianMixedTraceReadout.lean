/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianHermitianDeflation

/-! # Exact two-basis mixed trace readout

Independent real orthogonal eigenbases retain all overlap squares.
The mixed-power identity includes zero powers, so pure trace terms
and every compensation term use the same complete overlap kernel.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hamiltonian_orthogonal_diagonal_power
    (U : Matrix I I Real) (x : I -> Real)
    (hLeft : U.transpose * U = 1) (hRight : U * U.transpose = 1) (p : Nat) :
    (U * Matrix.diagonal x * U.transpose) ^ p =
      U * Matrix.diagonal (fun i => x i ^ p) * U.transpose := by
  induction p with
  | zero =>
      have hD0 : Matrix.diagonal (fun i => x i ^ 0) = (1 : Matrix I I Real) := by
        ext i j
        simp [Matrix.diagonal_apply, Matrix.one_apply]
      calc
        _ = 1 := pow_zero _
        _ = U * 1 * U.transpose := by rw [Matrix.mul_one, hRight]
        _ = _ := by rw [hD0]
  | succ p ih =>
      have hDiag : Matrix.diagonal (fun i => x i ^ p) * Matrix.diagonal x =
          Matrix.diagonal (fun i => x i ^ (p + 1)) := by
        ext i j
        by_cases hij : i = j
        case pos => subst j; simp [pow_succ]
        case neg => simp [hij]
      calc
        _ = (U * Matrix.diagonal x * U.transpose) ^ p *
            (U * Matrix.diagonal x * U.transpose) := pow_succ _ _
        _ = (U * Matrix.diagonal (fun i => x i ^ p) * U.transpose) *
            (U * Matrix.diagonal x * U.transpose) := by rw [ih]
        _ = U * (Matrix.diagonal (fun i => x i ^ p) *
            (U.transpose * U) * Matrix.diagonal x) * U.transpose := by
              simp only [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal (fun i => x i ^ p) * Matrix.diagonal x) *
            U.transpose := by rw [hLeft, Matrix.mul_one]
        _ = _ := by rw [hDiag]

theorem hamiltonian_two_basis_trace
    (U V : Matrix I I Real) (x y : I -> Real) :
    Matrix.trace ((U * Matrix.diagonal x * U.transpose) *
      (V * Matrix.diagonal y * V.transpose)) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        x i * y j * ((U.transpose * V) i j) ^ 2)) := by
  let W := U.transpose * V
  have hTrace :
      Matrix.trace ((U * Matrix.diagonal x * U.transpose) *
        (V * Matrix.diagonal y * V.transpose)) =
      Matrix.trace ((Matrix.diagonal x * W * Matrix.diagonal y) * W.transpose) := by
    calc
      _ = Matrix.trace (U *
          (Matrix.diagonal x * U.transpose * V * Matrix.diagonal y * V.transpose)) := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace
          ((Matrix.diagonal x * U.transpose * V * Matrix.diagonal y * V.transpose) * U) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by
        congr 1
        dsimp only [W]
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
        simp only [Matrix.mul_assoc]
  have hEntry (i : I) :
      ((Matrix.diagonal x * W * Matrix.diagonal y) * W.transpose) i i =
        Finset.univ.sum (fun j => x i * y j * (W i j) ^ 2) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hTrace]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i hi
  exact hEntry i

theorem hamiltonian_orthogonal_mixed_power_trace
    (U V : Matrix I I Real) (x y : I -> Real)
    (hUL : U.transpose * U = 1) (hUR : U * U.transpose = 1)
    (hVL : V.transpose * V = 1) (hVR : V * V.transpose = 1) (r s : Nat) :
    Matrix.trace ((U * Matrix.diagonal x * U.transpose) ^ r *
      (V * Matrix.diagonal y * V.transpose) ^ s) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        x i ^ r * y j ^ s * ((U.transpose * V) i j) ^ 2)) := by
  rw [hamiltonian_orthogonal_diagonal_power U x hUL hUR,
    hamiltonian_orthogonal_diagonal_power V y hVL hVR]
  exact hamiltonian_two_basis_trace U V (fun i => x i ^ r) (fun j => y j ^ s)

theorem hamiltonian_hermitian_mixed_power_trace
    (X Y : Matrix I I Real) (hX : X.IsHermitian) (hY : Y.IsHermitian) (r s : Nat) :
    Matrix.trace (X ^ r * Y ^ s) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        hX.eigenvalues i ^ r * hY.eigenvalues j ^ s *
          (((realGaussianEigenMatrix X hX).transpose *
            realGaussianEigenMatrix Y hY) i j) ^ 2)) := by
  let U := realGaussianEigenMatrix X hX
  let V := realGaussianEigenMatrix Y hY
  let x := hX.eigenvalues
  let y := hY.eigenvalues
  have hDX : X = U * Matrix.diagonal x * U.transpose :=
    realGaussianEigenMatrix_decomposition X hX
  have hDY : Y = V * Matrix.diagonal y * V.transpose :=
    realGaussianEigenMatrix_decomposition Y hY
  have hPX := congrArg (fun M : Matrix I I Real => M ^ r) hDX
  have hPY := congrArg (fun M : Matrix I I Real => M ^ s) hDY
  calc
    _ = Matrix.trace ((U * Matrix.diagonal x * U.transpose) ^ r *
        (V * Matrix.diagonal y * V.transpose) ^ s) := by
      rw [hPX, hPY]
    _ = _ := hamiltonian_orthogonal_mixed_power_trace U V x y
      (realGaussianEigenMatrix_orthogonal X hX)
      (hamiltonian_real_eigenmatrix_right_inverse X hX)
      (realGaussianEigenMatrix_orthogonal Y hY)
      (hamiltonian_real_eigenmatrix_right_inverse Y hY) r s

end PrimeFactorOscillations
