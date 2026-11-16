/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDeterminantEntryBudget
import PrimeFactorOscillations.Helpers.HamiltonianFiniteFactorTrace
import PrimeFactorOscillations.Helpers.HamiltonianRectangularMinors

/-! # Fixed-dimensional determinant updates retaining every Gram cross term -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota : Type*} [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota]

theorem hamiltonian_det_one_add_entry_bound
    (E : Matrix Jota Jota Real) (C : Real)
    (hEntry : forall i j, abs (E i j) <= C) :
    abs (Matrix.det (1 + E)) <=
      ((Fintype.card Jota).factorial : Real) * (1 + C) ^ Fintype.card Jota := by
  have hOne (i j : Jota) : abs ((1 : Matrix Jota Jota Real) i j) <= 1 := by
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have h := Matrix.det_le (abv := AbsoluteValue.abs)
    (fun i j => (abs_add_le ((1 : Matrix Jota Jota Real) i j) (E i j)).trans
      (add_le_add (hOne i j) (hEntry i j)))
  simpa only [AbsoluteValue.abs_apply, nsmul_eq_mul] using! h

theorem hamiltonian_det_one_add_norm_bound
    (E : Matrix Jota Jota Real) (C : Real) (hNorm : norm E <= C) :
    abs (Matrix.det (1 + E)) <=
      ((Fintype.card Jota).factorial : Real) * (1 + C) ^ Fintype.card Jota := by
  apply hamiltonian_det_one_add_entry_bound E C
  intro i j
  have h : abs (E i j) <= norm E := by
    simpa only [Real.norm_eq_abs] using l2_matrix_entry_le_norm E i j
  exact h.trans hNorm

theorem hamiltonian_determinant_right_inverse_update
    (M A : Matrix Iota Iota Real) (X : Matrix Iota Jota Real)
    (Y : Matrix Jota Iota Real) (hInv : M * A = 1) :
    Matrix.det (M + X * Y) / Matrix.det M = Matrix.det (1 + Y * A * X) := by
  have hDet : Matrix.det M * Matrix.det A = 1 := by
    rw [<- Matrix.det_mul, hInv, Matrix.det_one]
  have hNonzero : Not (Matrix.det M = 0) := by
    intro h
    rw [h, zero_mul] at hDet
    norm_num at hDet
  have hFactor : M * (1 + (A * X) * Y) = M + X * Y := by
    rw [Matrix.mul_add, Matrix.mul_one, <- Matrix.mul_assoc, <- Matrix.mul_assoc,
      hInv, Matrix.one_mul]
  have hUpdate : Matrix.det (M + X * Y) =
      Matrix.det M * Matrix.det (1 + Y * A * X) := by
    rw [<- hFactor, Matrix.det_mul, Matrix.det_one_add_mul_comm]
    rw [Matrix.mul_assoc]
  rw [hUpdate]
  field_simp

def hamiltonianGramUpdateLeft (R : Matrix Iota Iota Real)
    (U : Matrix Iota Jota Real) (V : Matrix Jota Iota Real) :
    Matrix Iota (Sum Jota Jota) Real :=
  fun i s => Sum.elim (fun a => (R.transpose * U) i a)
    (fun a => V.transpose i a) s

def hamiltonianGramUpdateRight (R : Matrix Iota Iota Real)
    (U : Matrix Iota Jota Real) (V : Matrix Jota Iota Real) :
    Matrix (Sum Jota Jota) Iota Real :=
  fun s j => Sum.elim (fun a => V a j)
    (fun a => (U.transpose * R + U.transpose * U * V) a j) s

theorem hamiltonian_gram_update_factorization
    (B R : Matrix Iota Iota Real) (U : Matrix Iota Jota Real)
    (V : Matrix Jota Iota Real) (hB : B = R + U * V) :
    B.transpose * B - R.transpose * R =
      hamiltonianGramUpdateLeft R U V * hamiltonianGramUpdateRight R U V := by
  have hProduct :
      hamiltonianGramUpdateLeft R U V * hamiltonianGramUpdateRight R U V =
        (R.transpose * U) * V +
          V.transpose * (U.transpose * R + U.transpose * U * V) := by
    ext i j
    change (Finset.univ.sum (fun s : Sum Jota Jota =>
      hamiltonianGramUpdateLeft R U V i s * hamiltonianGramUpdateRight R U V s j)) = _
    rw [Fintype.sum_sum_type]
    rfl
  rw [hProduct, hB, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.mul_assoc]
  abel

end PrimeFactorOscillations
