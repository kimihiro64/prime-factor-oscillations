/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFiniteFactorGramBound
import PrimeFactorOscillations.Helpers.HamiltonianSchurBudget

/-! # The constant projection is kept coupled in stochastic deletion norms -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_real_projection_norm
    (P : Matrix Iota Iota Real) (hSym : P.transpose = P) (hIdem : P * P = P) :
    norm P <= 1 := by
  have hConj : P.conjTranspose = P := by
    have he : P.conjTranspose = P.transpose := by ext i j; rfl
    exact he.trans hSym
  have h := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hConj, hIdem] at h
  nlinarith only [h, norm_nonneg P]

theorem hamiltonian_centering_projection_norm (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) :
    norm ((1 : Matrix Iota Iota Real) - averagingKernel q) <= 1 := by
  apply hamiltonian_real_projection_norm
  next =>
    rw [Matrix.transpose_sub, Matrix.transpose_one, averagingKernel_transpose]
  next =>
    rw [mul_sub, mul_one, sub_mul, one_mul, averagingKernel_mul_self q hq,
      sub_self, sub_zero]

theorem hamiltonian_nonnegative_regular_norm
    (M : Matrix Iota Iota Real) (r : Real) (hr : 0 <= r)
    (hRow : forall i, Finset.univ.sum (fun j => M i j) = r)
    (hCol : forall j, Finset.univ.sum (fun i => M i j) = r)
    (hNonneg : forall i j, 0 <= M i j) :
    norm M <= r := by
  apply hamiltonian_l2_row_column_budget M r hr
  next =>
    intro i
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hNonneg i _)] using (hRow i).le
  next =>
    intro j
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hNonneg _ j)] using (hCol j).le

theorem hamiltonian_regular_averaging_product
    (M : Matrix Iota Iota Real) (q r : Real)
    (hRow : forall i, Finset.univ.sum (fun j => M i j) = r) :
    M * averagingKernel q = SMul.smul r (averagingKernel q) := by
  ext i j
  change Finset.univ.sum (fun k => M i k * q) = r * q
  rw [<- Finset.sum_mul, hRow i]

theorem hamiltonian_regular_centered_contraction
    (M : Matrix Iota Iota Real) (q r : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (hr : 0 <= r)
    (hRow : forall i, Finset.univ.sum (fun j => M i j) = r)
    (hCol : forall j, Finset.univ.sum (fun i => M i j) = r)
    (hNonneg : forall i j, 0 <= M i j) :
    norm (M - SMul.smul r (averagingKernel q)) <= r := by
  have hNorm := hamiltonian_nonnegative_regular_norm M r hr hRow hCol hNonneg
  have hP := hamiltonian_centering_projection_norm q hq
  have hFactor : M - SMul.smul r (averagingKernel q) =
      M * (1 - averagingKernel q) := by
    rw [mul_sub, mul_one, hamiltonian_regular_averaging_product M q r hRow]
  rw [hFactor]
  calc
    _ <= norm M * norm (1 - averagingKernel q) := Matrix.l2_opNorm_mul _ _
    _ <= r * 1 := mul_le_mul hNorm hP (norm_nonneg _) hr
    _ = r := mul_one _

theorem stochastic_centered_contraction
    (T : Matrix Iota Iota Real) (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) :
    norm (centeredKernel T q) <= 1 := by
  have h := hamiltonian_regular_centered_contraction T q 1 hq (by norm_num)
    hRow hCol hNonneg
  have he : SMul.smul (1 : Real) (averagingKernel (Iota := Iota) q) =
      averagingKernel q := by
    ext i j
    change 1 * q = q
    ring
  rw [he] at h
  exact h

end PrimeFactorOscillations
