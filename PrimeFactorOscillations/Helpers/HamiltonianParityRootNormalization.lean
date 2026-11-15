/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianParityRootRegularization

/-! # Exact normalization of the regularized parity determinant

The constant-direction rank-one factor is separated algebraically.
Every centered block is retained, and no inverse of the singular
physical kernel is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem stochastic_regularized_root_matrix_factor (T : Matrix Iota Iota Real)
    (q : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    hamiltonianParityRegularizedKernel T q 0 =
      ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
        bipartiteLift (centeredKernel T q)) *
      (1 + averagingKernel (Iota := Sum Iota Iota) (q / 2)) := by
  have hCenteredRow (i : Iota) :
      Finset.univ.sum (fun j => centeredKernel T q i j) = 0 := by
    simp only [centeredKernel, Matrix.sub_apply, Finset.sum_sub_distrib,
      hRow i, averagingKernel, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hCenteredCol (j : Iota) :
      Finset.univ.sum (fun i => centeredKernel T q i j) = 0 := by
    simp only [centeredKernel, Matrix.sub_apply, Finset.sum_sub_distrib,
      hCol j, averagingKernel, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hOrth : bipartiteLift (centeredKernel T q) *
      averagingKernel (Iota := Sum Iota Iota) (q / 2) = 0 := by
    apply Matrix.ext
    intro i j
    cases i <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, bipartiteLift,
        Matrix.fromBlocks, averagingKernel, <- Finset.sum_mul,
        hCenteredRow, hCenteredCol]
  rw [mul_add, mul_one, add_mul, one_mul, hOrth, add_zero]
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [hamiltonianParityRegularizedKernel, zero_smul, sub_zero,
      Matrix.add_apply, Matrix.sub_apply, bipartiteLift, Matrix.fromBlocks,
      Matrix.transpose_apply, centeredKernel, averagingKernel,
      hamiltonianParityProjection, hamiltonianParitySign, Matrix.zero_apply]
    <;> ring

theorem stochastic_regularized_root_determinant (T : Matrix Iota Iota Real)
    (q : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    Matrix.det (hamiltonianParityRegularizedKernel T q 0) =
      2 * Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q) := by
  have hFull : (Fintype.card (Sum Iota Iota) : Real) * (q / 2) = 1 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hConstant :
      Matrix.det ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
        averagingKernel (q / 2)) = 2 := by
    have h := det_one_sub_averagingKernel (Iota := Sum Iota Iota) (q / 2) hFull (-1)
    norm_num only [neg_smul, one_smul, sub_neg_eq_add] at h
    exact h
  rw [stochastic_regularized_root_matrix_factor T q hq hRow hCol,
    Matrix.det_mul, hConstant]
  have hBipartite := det_one_add_bipartiteLift (centeredKernel T q) (1 : Real)
  simp only [one_smul, one_pow] at hBipartite
  rw [hBipartite, mul_comm]

end PrimeFactorOscillations
