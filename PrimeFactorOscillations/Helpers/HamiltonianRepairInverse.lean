/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRepairKernel

/-! # The exact parity-corrected inverse identity

The actual kernel K is a right inverse of I+P on the parity-orthogonal
subspace. Constant and parity corrections are evaluated with their
coefficients intact before any nonlinear scaling remainder is bounded.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianParityProjection (q : Real) :
    Matrix (Sum Iota Iota) (Sum Iota Iota) Real :=
  fun i j => q / 2 * hamiltonianParitySign i * hamiltonianParitySign j

theorem hamiltonianParityProjection_eq (q : Real) :
    hamiltonianParityProjection (Iota := Iota) q =
      averagingKernel (Iota := Sum Iota Iota) (q / 2) -
        bipartiteLift (averagingKernel (Iota := Iota) q) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [hamiltonianParityProjection, hamiltonianParitySign, averagingKernel,
      bipartiteLift, Matrix.fromBlocks, Matrix.sub_apply] <;> ring

variable [Nonempty Iota]

theorem stochastic_repair_kernel_right_inverse (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + bipartiteLift T) *
        hamiltonianRepairKernel T q =
      1 - hamiltonianParityProjection q := by
  let B := centeredKernel T q
  let P := bipartiteLift T
  let Q := bipartiteLift B
  let A := bipartiteLift (averagingKernel (Iota := Iota) q)
  let C := averagingKernel (Iota := Sum Iota Iota) (q / 2)
  let M : Matrix (Sum Iota Iota) (Sum Iota Iota) Real := 1 + Q
  let R := Ring.inverse M
  let H := hamiltonianRepairProjection (Iota := Iota) q
  have hBRow (i : Iota) : Finset.sum Finset.univ (fun j => B i j) = 0 := by
    change Finset.sum Finset.univ (fun j => T i j - q) = 0
    rw [Finset.sum_sub_distrib, hRow i, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hBCol (j : Iota) : Finset.sum Finset.univ (fun i => B i j) = 0 := by
    change Finset.sum Finset.univ (fun i => T i j - q) = 0
    rw [Finset.sum_sub_distrib, hCol j, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hPRow : forall i, Finset.sum Finset.univ (fun j => P i j) = 1 := by
    intro i
    cases i with
    | inl i =>
      simpa [P, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type] using hRow i
    | inr j =>
      simpa [P, bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply,
        Fintype.sum_sum_type] using hCol j
  have hPC : P * C = C := mul_averagingKernel_of_rowSum P (q / 2) hPRow
  have hPA : P * A = HSMul.hSMul (2 : Real) C - A := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [P, A, C, Matrix.mul_apply, Fintype.sum_sum_type, bipartiteLift,
        Matrix.fromBlocks, averagingKernel, Matrix.transpose_apply,
        <- Finset.sum_mul, hRow, hCol, Matrix.smul_apply, smul_eq_mul] <;> ring
  have hAQ : A * Q = 0 := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [A, Q, Matrix.mul_apply, Fintype.sum_sum_type, bipartiteLift,
        Matrix.fromBlocks, averagingKernel, Matrix.transpose_apply,
        <- Finset.mul_sum, hBRow, hBCol]
  have hPQ : P = Q + A := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [P, Q, A, B, bipartiteLift, Matrix.fromBlocks, centeredKernel,
        averagingKernel, Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply]
  have hQNorm : norm Q <= rho := le_trans (bipartiteLift_l2_norm_le B) hNorm
  have hUnit : IsUnit M := by
    have hNeg : norm (-Q) < 1 := by
      rw [norm_neg]
      exact lt_of_le_of_lt hQNorm hRho
    simpa only [M, sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hNeg
  have hMR : M * R = 1 := Ring.mul_inverse_cancel _ hUnit
  have hAM : A * M = A := by
    dsimp only [M]
    rw [mul_add, mul_one, hAQ, add_zero]
  have hAR : A * R = A := by
    calc
      _ = (A * M) * R := by rw [hAM]
      _ = A * (M * R) := mul_assoc _ _ _
      _ = A := by rw [hMR, mul_one]
  have hPR : (1 + P) * R = 1 + A := by
    rw [hPQ, <- add_assoc, add_mul, hMR, hAR]
  have hH : H = HSMul.hSMul (3 / 2 : Real) C - A := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [H, hamiltonianRepairProjection, hamiltonianParitySign, C, A,
        averagingKernel, bipartiteLift, Matrix.fromBlocks, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul] <;> ring
  have hOnePC : (1 + P) * C = HSMul.hSMul (2 : Real) C := by
    rw [add_mul, one_mul, hPC]
    apply Matrix.ext
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hOnePA : (1 + P) * A = HSMul.hSMul (2 : Real) C := by
    rw [add_mul, one_mul, hPA]
    abel
  have hOnePH : (1 + P) * H = C := by
    rw [hH, mul_sub, Matrix.mul_smul, hOnePC, hOnePA]
    apply Matrix.ext
    intro i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  change (1 + P) * (R - H) = 1 - hamiltonianParityProjection q
  rw [mul_sub, hPR, hOnePH, hamiltonianParityProjection_eq]
  change 1 + A - C = 1 - (C - A)
  abel

end PrimeFactorOscillations
