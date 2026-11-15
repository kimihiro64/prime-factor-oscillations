/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Matrix.Normed
import PrimeFactorOscillations.Helpers.HamiltonianNeumannBound

/-! # A finite row-norm inverse for the deleted-coordinate boundary

The operator norm in this file is explicitly the maximum absolute row
sum. The conclusion uses row sums again, so consumers need no implicit
choice between this norm and the Euclidean spectral norm.
Empty index types are included.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem matrix_row_operator_norm_le (M : Matrix Iota Iota Real) (b : Real)
    (hb : 0 <= b)
    (hRow : forall i, Finset.sum Finset.univ (fun j => abs (M i j)) <= b) :
    norm M <= b := by
  have hRowNN (i : Iota) :
      Finset.sum Finset.univ (fun j => nnnorm (M i j)) <= Real.toNNReal b := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs,
      Real.coe_toNNReal b hb] using hRow i
  rw [Matrix.linfty_opNorm_def]
  have hSup := Finset.sup_le (fun i (_ : Membership.mem Finset.univ i) => hRowNN i)
  exact (NNReal.coe_le_coe.mpr hSup).trans_eq (Real.coe_toNNReal b hb)

theorem matrix_row_sum_le_operator_norm (M : Matrix Iota Iota Real) (i : Iota) :
    Finset.sum Finset.univ (fun j => abs (M i j)) <= norm M := by
  rw [Matrix.linfty_opNorm_def]
  have h := Finset.le_sup (f := fun k => Finset.sum Finset.univ
    (fun j => nnnorm (M k j))) (Finset.mem_univ i)
  simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using
    (NNReal.coe_le_coe.mpr h)

theorem matrix_row_neumann_inverse (M : Matrix Iota Iota Real) (theta : Real)
    (hTheta0 : 0 <= theta) (hTheta1 : theta < 1)
    (hRow : forall i, Finset.sum Finset.univ
      (fun j => abs ((M - 1) i j)) <= theta) :
    IsUnit M /\ forall i, (1 - theta) * Finset.sum Finset.univ
      (fun j => abs (Ring.inverse M i j)) <= 1 := by
  have hDiff : norm (M - 1) <= theta :=
    matrix_row_operator_norm_le (M - 1) theta hTheta0 hRow
  have hNeg : norm (1 - M) <= theta := by
    rw [<- neg_sub M 1, norm_neg]
    exact hDiff
  have hUnit : IsUnit M := by
    have h := isUnit_one_sub_of_norm_lt_one (lt_of_le_of_lt hNeg hTheta1)
    simpa only [sub_sub_cancel] using h
  have hOne : norm (1 : Matrix Iota Iota Real) <= 1 := by
    apply matrix_row_operator_norm_le _ 1 (by norm_num)
    intro i
    simp [Matrix.one_apply, abs_ite]
  have hInv : (1 - theta) * norm (Ring.inverse M) <= 1 := by
    have h := neumann_norm_certificate (1 - M) theta hNeg hTheta1
    simpa only [sub_sub_cancel] using le_trans h hOne
  refine And.intro hUnit ?_
  intro i
  exact le_trans
    (mul_le_mul_of_nonneg_left (matrix_row_sum_le_operator_norm (Ring.inverse M) i)
      (le_of_lt (sub_pos.mpr hTheta1))) hInv

theorem matrix_row_half_inverse (M : Matrix Iota Iota Real)
    (hRow : forall i, Finset.sum Finset.univ
      (fun j => abs ((M - 1) i j)) <= 1 / 2) :
    IsUnit M /\ forall i, Finset.sum Finset.univ
      (fun j => abs (Ring.inverse M i j)) <= 2 := by
  have h := matrix_row_neumann_inverse M (1 / 2) (by norm_num) (by norm_num) hRow
  refine And.intro h.1 ?_
  intro i
  have hi := h.2 i
  linarith

end PrimeFactorOscillations
