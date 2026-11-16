/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceTaylorSeries

/-! # Fixed-factor trace compensation with coefficient one on the full energy

The low-dimensional mixed traces are kept before their bounds. Their cost
depends on the fixed factor dimension, not the ambient matrix order.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota : Type*} [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota]

theorem hamiltonian_matrix_trace_norm_bound (M : Matrix Jota Jota Real) :
    abs (Matrix.trace M) <= (Fintype.card Jota : Real) * norm M := by
  change abs (Finset.univ.sum (fun i => M i i)) <= _
  calc
    _ <= Finset.univ.sum (fun i => abs (M i i)) := Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.univ.sum (fun _ : Jota => norm M) := Finset.sum_le_sum (fun i _ => by
      simpa only [Real.norm_eq_abs] using l2_matrix_entry_le_norm M i i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem hamiltonian_finite_factor_trace_identity
    (B R : Matrix Iota Iota Real) (U : Matrix Iota Jota Real) (V : Matrix Jota Iota Real)
    (hB : B = R + U * V) :
    Matrix.trace (R.transpose * R) =
      Matrix.trace (B.transpose * B) - 2 * Matrix.trace (V * B.transpose * U) +
        Matrix.trace ((U.transpose * U) * (V * V.transpose)) := by
  have hR : R = B - U * V := by rw [hB]; abel
  have h1 : Matrix.trace (B.transpose * (U * V)) =
      Matrix.trace (V * B.transpose * U) := by
    calc
      _ = Matrix.trace ((B.transpose * U) * V) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (V * (B.transpose * U)) := Matrix.trace_mul_comm _ _
      _ = _ := by rw [Matrix.mul_assoc]
  have h2 : Matrix.trace ((V.transpose * U.transpose) * B) =
      Matrix.trace (V * B.transpose * U) := by
    have he : (B.transpose * (U * V)).transpose = (V.transpose * U.transpose) * B := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [<- he, Matrix.trace_transpose, h1]
  have h3 : Matrix.trace ((V.transpose * U.transpose) * (U * V)) =
      Matrix.trace ((U.transpose * U) * (V * V.transpose)) := by
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm V.transpose (U.transpose * U * V)
  rw [hR, Matrix.transpose_sub, Matrix.transpose_mul, sub_mul, mul_sub, mul_sub,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, h1, h2, h3]
  ring

theorem hamiltonian_finite_factor_energy_identity
    (B R : Matrix Iota Iota Real) (U : Matrix Iota Jota Real) (V : Matrix Jota Iota Real)
    (hB : B = R + U * V) :
    Finset.univ.sum (fun i => Finset.univ.sum (fun j => R i j ^ 2)) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => B i j ^ 2)) -
        2 * Matrix.trace (V * B.transpose * U) +
        Matrix.trace ((U.transpose * U) * (V * V.transpose)) := by
  have hEnergy (M : Matrix Iota Iota Real) :
      Matrix.trace (M.transpose * M) =
        Finset.univ.sum (fun i => Finset.univ.sum (fun j => M i j ^ 2)) := by
    change Finset.univ.sum (fun i => Finset.univ.sum (fun j => M j i * M j i)) = _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h := hamiltonian_finite_factor_trace_identity B R U V hB
  rw [hEnergy R, hEnergy B] at h
  exact h

theorem hamiltonian_finite_factor_energy_bound
    (B R : Matrix Iota Iota Real) (U : Matrix Iota Jota Real) (V : Matrix Jota Iota Real)
    (rho L : Real) (hRho : 0 <= rho) (hL : 0 <= L)
    (hB : B = R + U * V) (hNormB : norm B <= rho)
    (hNormU : norm U <= L) (hNormV : norm V <= L) :
    Finset.univ.sum (fun i => Finset.univ.sum (fun j => R i j ^ 2)) <=
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => B i j ^ 2)) +
        2 * (Fintype.card Jota : Real) * rho * L ^ 2 +
          (Fintype.card Jota : Real) * L ^ 4 := by
  have hBt : norm B.transpose <= rho := by
    have he : B.conjTranspose = B.transpose := by ext i j; rfl
    rw [<- he, Matrix.l2_opNorm_conjTranspose]
    exact hNormB
  have hUt : norm U.transpose <= L := by
    have he : U.conjTranspose = U.transpose := by ext i j; rfl
    rw [<- he, Matrix.l2_opNorm_conjTranspose]
    exact hNormU
  have hVt : norm V.transpose <= L := by
    have he : V.conjTranspose = V.transpose := by ext i j; rfl
    rw [<- he, Matrix.l2_opNorm_conjTranspose]
    exact hNormV
  have hVB : norm (V * B.transpose) <= L * rho := by
    calc
      _ <= norm V * norm B.transpose := Matrix.l2_opNorm_mul _ _
      _ <= L * norm B.transpose :=
        mul_le_mul_of_nonneg_right hNormV (norm_nonneg _)
      _ <= _ := mul_le_mul_of_nonneg_left hBt hL
  have hCross : norm (V * B.transpose * U) <= rho * L ^ 2 := by
    calc
      _ <= norm (V * B.transpose) * norm U := Matrix.l2_opNorm_mul _ _
      _ <= (L * rho) * norm U := mul_le_mul_of_nonneg_right hVB (norm_nonneg _)
      _ <= (L * rho) * L :=
        mul_le_mul_of_nonneg_left hNormU (mul_nonneg hL hRho)
      _ = _ := by ring
  have hUU : norm (U.transpose * U) <= L * L := by
    calc
      _ <= norm U.transpose * norm U := Matrix.l2_opNorm_mul _ _
      _ <= L * norm U := mul_le_mul_of_nonneg_right hUt (norm_nonneg _)
      _ <= _ := mul_le_mul_of_nonneg_left hNormU hL
  have hVV : norm (V * V.transpose) <= L * L := by
    calc
      _ <= norm V * norm V.transpose := Matrix.l2_opNorm_mul _ _
      _ <= L * norm V.transpose := mul_le_mul_of_nonneg_right hNormV (norm_nonneg _)
      _ <= _ := mul_le_mul_of_nonneg_left hVt hL
  have hQuad : norm ((U.transpose * U) * (V * V.transpose)) <= L ^ 4 := by
    calc
      _ <= norm (U.transpose * U) * norm (V * V.transpose) := Matrix.l2_opNorm_mul _ _
      _ <= (L * L) * (L * L) :=
        mul_le_mul hUU hVV (norm_nonneg _) (mul_nonneg hL hL)
      _ = _ := by ring
  have hTraceCross : abs (Matrix.trace (V * B.transpose * U)) <=
      (Fintype.card Jota : Real) * (rho * L ^ 2) :=
    (hamiltonian_matrix_trace_norm_bound (V * B.transpose * U)).trans
      (mul_le_mul_of_nonneg_left hCross (Nat.cast_nonneg _))
  have hTraceQuad : Matrix.trace ((U.transpose * U) * (V * V.transpose)) <=
      (Fintype.card Jota : Real) * L ^ 4 :=
    (le_abs_self _).trans ((hamiltonian_matrix_trace_norm_bound
      ((U.transpose * U) * (V * V.transpose))).trans
        (mul_le_mul_of_nonneg_left hQuad (Nat.cast_nonneg _)))
  have hLower := (abs_le.mp hTraceCross).1
  rw [hamiltonian_finite_factor_energy_identity B R U V hB]
  linarith only [hLower, hTraceQuad]

end PrimeFactorOscillations
