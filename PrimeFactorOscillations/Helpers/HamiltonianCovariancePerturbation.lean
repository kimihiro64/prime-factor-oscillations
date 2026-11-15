/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Abel
import PrimeFactorOscillations.Helpers.HamiltonianFiniteRowInverse

/-! # Actual covariance inverse perturbation with row budgets

This controls only the explicit inverse perturbation remainder.
The original signed covariance and its first correction remain intact.
Empty retained supports are permitted.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_matrix_product_row_bound
    (A B : Matrix Iota Iota Real) (a b : Real) (ha : 0 <= a) (hb : 0 <= b)
    (hA : forall i, Finset.sum Finset.univ (fun j => abs (A i j)) <= a)
    (hB : forall i, Finset.sum Finset.univ (fun j => abs (B i j)) <= b) (i : Iota) :
    Finset.sum Finset.univ (fun j => abs ((A * B) i j)) <= a * b := by
  have hANorm := matrix_row_operator_norm_le A a ha hA
  have hBNorm := matrix_row_operator_norm_le B b hb hB
  calc
    _ <= norm (A * B) := matrix_row_sum_le_operator_norm (A * B) i
    _ <= norm A * norm B := norm_mul_le A B
    _ <= a * b := mul_le_mul hANorm hBNorm (norm_nonneg B) ha

theorem hamiltonian_matrix_product_entry_row_bound
    (A B : Matrix Iota Iota Real) (b eps : Real) (hEps : 0 <= eps)
    (hA : forall i, Finset.sum Finset.univ (fun k => abs (A i k)) <= b)
    (hB : forall i j, abs (B i j) <= eps) (i j : Iota) :
    abs ((A * B) i j) <= b * eps := by
  rw [Matrix.mul_apply]
  calc
    _ <= Finset.sum Finset.univ (fun k => abs (A i k * B k j)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = Finset.sum Finset.univ (fun k => abs (A i k) * abs (B k j)) := by
      simp only [abs_mul]
    _ <= Finset.sum Finset.univ (fun k => abs (A i k) * eps) :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hB k j) (abs_nonneg _))
    _ = Finset.sum Finset.univ (fun k => abs (A i k)) * eps := by
      rw [Finset.sum_mul]
    _ <= b * eps := mul_le_mul_of_nonneg_right (hA i) hEps

theorem hamiltonian_actual_inverse_perturbation
    (M J E : Matrix Iota Iota Real) (b eps : Real) (hb : 0 <= b) (hEps : 0 <= eps)
    (hInverse : M * J = 1)
    (hJ : forall i, Finset.sum Finset.univ (fun j => abs (J i j)) <= b)
    (hJE : forall i j, abs ((J * E) i j) <= eps)
    (hEJ : forall i j, abs ((E * J) i j) <= eps)
    (hSmall : (Fintype.card Iota : Real) * eps <= 1 / 2) :
    IsUnit (M + E) /\
    (forall i, Finset.sum Finset.univ
      (fun j => abs (Ring.inverse (M + E) i j)) <= 2 * b) /\
    forall i j, abs ((Ring.inverse (M + E) - J) i j) <= 2 * b * eps := by
  let F := (1 : Matrix Iota Iota Real) + J * E
  let K := Ring.inverse F * J
  have hDiffF : F - 1 = J * E := by
    dsimp only [F]
    abel
  have hRowF (i : Iota) :
      Finset.sum Finset.univ (fun j => abs ((F - 1) i j)) <= 1 / 2 := by
    rw [hDiffF]
    calc
      _ <= Finset.sum Finset.univ (fun _ : Iota => eps) :=
        Finset.sum_le_sum (fun j _ => hJE i j)
      _ = (Fintype.card Iota : Real) * eps := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ <= _ := hSmall
  have hInvF := matrix_row_half_inverse F hRowF
  have hFactor : M * F = M + E := by
    dsimp only [F]
    rw [mul_add, mul_one, <- mul_assoc, hInverse, one_mul]
  have hRight : (M + E) * K = 1 := by
    calc
      _ = M * (F * Ring.inverse F) * J := by
        dsimp only [K]
        rw [<- hFactor]
        simp only [mul_assoc]
      _ = 1 := by rw [Ring.mul_inverse_cancel F hInvF.1, mul_one, hInverse]
  have hUnit : IsUnit (M + E) :=
    (Matrix.isUnit_iff_isUnit_det (M + E)).mpr (Matrix.isUnit_det_of_right_inverse hRight)
  have hActual : Ring.inverse (M + E) = K := by
    calc
      _ = Ring.inverse (M + E) * ((M + E) * K) := by rw [hRight, mul_one]
      _ = K := by rw [<- mul_assoc, Ring.inverse_mul_cancel (M + E) hUnit, one_mul]
  have hKRow (i : Iota) :
      Finset.sum Finset.univ (fun j => abs (K i j)) <= 2 * b :=
    hamiltonian_matrix_product_row_bound (Ring.inverse F) J 2 b
      (by norm_num) hb hInvF.2 hJ i
  have hLeft : K * (M + E) = 1 := _root_.mul_eq_one_comm.mp hRight
  have hEq : K + K * (E * J) = J := by
    have h := congrArg (fun A : Matrix Iota Iota Real => A * J) hLeft
    rw [one_mul, mul_add, add_mul, mul_assoc K M J, hInverse, mul_one,
      mul_assoc K E J] at h
    exact h
  have hDifference : K - J = -(K * (E * J)) := by
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      _ = (K + K * (E * J)) - J := by abel
      _ = 0 := by rw [hEq, sub_self]
  refine And.intro hUnit (And.intro ?_ ?_)
  case refine_1 =>
    intro i
    rw [hActual]
    exact hKRow i
  case refine_2 =>
    intro i j
    rw [hActual, hDifference, Matrix.neg_apply, abs_neg]
    exact hamiltonian_matrix_product_entry_row_bound K (E * J) (2 * b) eps
      hEps hKRow hEJ i j

end PrimeFactorOscillations
