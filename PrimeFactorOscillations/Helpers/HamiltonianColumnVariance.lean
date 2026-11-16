/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianTraceBounds
import PrimeFactorOscillations.Helpers.HamiltonianSignFlipMoments

/-! # The actual column variance budget in signed trace moments

The full column-square variance factors exactly as a weighted Gram
operator. Even-power sandwich diagonals are nonnegative. The column
budget is applied to that joint trace before the spectral contraction.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

def hamiltonianColumnSummand (E : Matrix I I Real) (j : I) : Matrix I I Real :=
  fun r s => (1 / 2 : Real) * E r j * E s j

def hamiltonianColumnEnergy (E : Matrix I I Real) (j : I) : Real :=
  Finset.univ.sum (fun r => E r j ^ 2)

theorem hamiltonian_column_summand_hermitian (E : Matrix I I Real) (j : I) :
    (hamiltonianColumnSummand E j).IsHermitian := by
  change (hamiltonianColumnSummand E j).conjTranspose = hamiltonianColumnSummand E j
  ext r s
  simp only [Matrix.conjTranspose_apply]
  change (1 / 2 : Real) * E s j * E r j = (1 / 2 : Real) * E r j * E s j
  ring

theorem hamiltonian_column_summand_square_entry
    (E : Matrix I I Real) (j r s : I) :
    (hamiltonianColumnSummand E j ^ 2) r s =
      (1 / 4 : Real) * hamiltonianColumnEnergy E j * (E r j * E s j) := by
  simp only [pow_two, Matrix.mul_apply, hamiltonianColumnSummand]
  calc
    _ = Finset.univ.sum (fun i => ((1 / 4 : Real) * (E r j * E s j)) * E i j ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [<- Finset.mul_sum]; unfold hamiltonianColumnEnergy; ring

theorem hamiltonian_column_variance_factorization (E : Matrix I I Real) :
    hamiltonianSignVariance (hamiltonianColumnSummand E) =
      SMul.smul (1 / 4 : Real)
        (E * Matrix.diagonal (hamiltonianColumnEnergy E) * E.transpose) := by
  ext r s
  simp only [hamiltonianSignVariance, Matrix.sum_apply,
    hamiltonian_column_summand_square_entry, hamiltonian_sign_smul_entry]
  rw [Matrix.mul_apply, Finset.mul_sum]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem hamiltonian_even_sandwich_diagonal_nonnegative
    (E Z : Matrix I I Real) (hZ : Z.IsHermitian)
    (q : Nat) (hEven : Even q) (j : I) :
    0 <= (E.transpose * Z ^ q * E) j j := by
  let r := hEven.choose
  have hQ : q = r + r := hEven.choose_spec
  have hZT : Z.transpose = Z := by
    ext i k
    have h : Z.conjTranspose = Z := hZ
    simpa using congrArg (fun M : Matrix I I Real => M i k) h
  let B := Z ^ r
  have hBT : B.transpose = B := by
    dsimp only [B]
    rw [Matrix.transpose_pow, hZT]
  have hBsq : B * B = Z ^ q := by
    dsimp only [B]
    rw [<- pow_add, <- hQ]
  have hGram : E.transpose * Z ^ q * E = (B * E).transpose * (B * E) := by
    rw [Matrix.transpose_mul, hBT, <- hBsq]
    simp only [Matrix.mul_assoc]
  rw [hGram, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  exact Finset.sum_nonneg (fun i hi => mul_self_nonneg ((B * E) i j))

theorem hamiltonian_column_variance_trace_budget
    (E Z : Matrix I I Real) (hE : E.IsHermitian) (hZ : Z.IsHermitian)
    (alpha : Real) (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (q : Nat) (hEven : Even q) :
    Matrix.trace (hamiltonianSignVariance (hamiltonianColumnSummand E) * Z ^ q) <=
      (alpha / 4) * Matrix.trace (E ^ 2 * Z ^ q) := by
  let w := hamiltonianColumnEnergy E
  let T := E.transpose * Z ^ q * E
  have hET : E.transpose = E := by
    ext i k
    have h : E.conjTranspose = E := hE
    simpa using congrArg (fun M : Matrix I I Real => M i k) h
  have hCyclic :
      Matrix.trace ((E * Matrix.diagonal w * E.transpose) * Z ^ q) =
        Matrix.trace (Matrix.diagonal w * T) := by
    calc
      _ = Matrix.trace (E * (Matrix.diagonal w * E.transpose * Z ^ q)) := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Matrix.diagonal w * E.transpose * Z ^ q) * E) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by dsimp only [T]; congr 1; simp only [Matrix.mul_assoc]
  have hDiag : Matrix.trace (Matrix.diagonal w * T) =
      Finset.univ.sum (fun j => w j * T j j) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  have hSum : Finset.univ.sum (fun j => w j * T j j) <=
      alpha * Finset.univ.sum (fun j => T j j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (hColumn j)
      (hamiltonian_even_sandwich_diagonal_nonnegative E Z hZ q hEven j)
  have hTrace : Finset.univ.sum (fun j => T j j) = Matrix.trace (E ^ 2 * Z ^ q) := by
    change Matrix.trace T = _
    calc
      _ = Matrix.trace (E * (E.transpose * Z ^ q)) := Matrix.trace_mul_comm _ _
      _ = _ := by rw [hET, pow_two]; simp only [Matrix.mul_assoc]
  rw [hamiltonian_column_variance_factorization, hamiltonian_trace_scaled_left]
  change (1 / 4 : Real) * Matrix.trace ((E * Matrix.diagonal w * E.transpose) * Z ^ q) <= _
  rw [hCyclic, hDiag]
  have h := mul_le_mul_of_nonneg_left hSum (show (0 : Real) <= 1 / 4 by norm_num)
  rw [hTrace] at h
  convert h using 1 <;> ring

theorem hamiltonian_contraction_even_trace_product
    (E Z : Matrix I I Real) (hE : E.IsHermitian) (hZ : Z.IsHermitian)
    (hNorm : norm E <= 1) (q : Nat) (hEven : Even q) :
    Matrix.trace (E ^ 2 * Z ^ q) <= Matrix.trace (Z ^ q) := by
  let w := fun i j => (((realGaussianEigenMatrix E hE).transpose *
    realGaussianEigenMatrix Z hZ) i j) ^ 2
  have hRead := hamiltonian_hermitian_mixed_power_trace E Z hE hZ 2 q
  have hPure : Matrix.trace (Z ^ q) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        hZ.eigenvalues j ^ q * w i j)) := by
    simpa only [pow_zero, Matrix.one_mul, one_mul] using
      hamiltonian_hermitian_mixed_power_trace E Z hE hZ 0 q
  rw [hRead, hPure]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have hAbs := (realGaussianEigenvalue_abs_le_norm E hE i).trans hNorm
  have hSq : hE.eigenvalues i ^ 2 <= 1 := by
    have h0 := abs_nonneg (hE.eigenvalues i)
    have hs := sq_abs (hE.eigenvalues i)
    nlinarith only [hAbs, h0, hs]
  let r := hEven.choose
  have hQ : q = r + r := hEven.choose_spec
  have hZq : 0 <= hZ.eigenvalues j ^ q := by
    rw [hQ, pow_add]
    exact mul_self_nonneg _
  have hWeight : 0 <= hZ.eigenvalues j ^ q * w i j :=
    mul_nonneg hZq (sq_nonneg _)
  calc
    _ = hE.eigenvalues i ^ 2 * (hZ.eigenvalues j ^ q * w i j) := by ring
    _ <= 1 * (hZ.eigenvalues j ^ q * w i j) :=
      mul_le_mul_of_nonneg_right hSq hWeight
    _ = _ := one_mul _

theorem hamiltonian_column_variance_even_trace_bound
    (E Z : Matrix I I Real) (hE : E.IsHermitian) (hZ : Z.IsHermitian)
    (alpha : Real) (hAlpha : 0 <= alpha)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hNorm : norm E <= 1) (q : Nat) (hEven : Even q) :
    Matrix.trace (hamiltonianSignVariance (hamiltonianColumnSummand E) * Z ^ q) <=
      (alpha / 4) * Matrix.trace (Z ^ q) := by
  exact (hamiltonian_column_variance_trace_budget E Z hE hZ alpha hColumn q hEven).trans
    (mul_le_mul_of_nonneg_left
      (hamiltonian_contraction_even_trace_product E Z hE hZ hNorm q hEven)
      (div_nonneg hAlpha (by norm_num)))

theorem hamiltonian_column_sign_moment_recurrence
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha : Real) (hAlpha : 0 <= alpha)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hNorm : norm E <= 1) (q : Nat) (hEven : Even q) :
    Finset.univ.sum (fun e => Matrix.trace
      (hamiltonianSignMatrix (hamiltonianColumnSummand E) e ^ (q + 2))) <=
      (((q + 1 : Nat) : Real) * (alpha / 4)) *
        Finset.univ.sum (fun e => Matrix.trace
          (hamiltonianSignMatrix (hamiltonianColumnSummand E) e ^ q)) := by
  let A := hamiltonianColumnSummand E
  have hA : forall j, (A j).IsHermitian := hamiltonian_column_summand_hermitian E
  have hMain := hamiltonian_sign_trace_moment_variance_bound A hA q hEven
  have hBudget := Finset.sum_le_sum (s := Finset.univ) (fun e he =>
    hamiltonian_column_variance_even_trace_bound E (hamiltonianSignMatrix A e)
      hE (hamiltonian_sign_matrix_hermitian A hA e) alpha hAlpha hColumn hNorm q hEven)
  rw [<- Finset.mul_sum] at hBudget
  have h := hMain.trans
    (mul_le_mul_of_nonneg_left hBudget (Nat.cast_nonneg (q + 1)))
  simpa only [mul_assoc] using h

end PrimeFactorOscillations
