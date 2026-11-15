/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRepairInverse

/-! # Symmetry and the exact null direction of the repair kernel

These identities permit a boundary Schur correction without a spurious
inverse in the bipartite parity direction. They retain the actual kernel.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_repair_kernel_transpose (T : Matrix Iota Iota Real)
    (q rho : Real) (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    (hamiltonianRepairKernel T q).transpose = hamiltonianRepairKernel T q := by
  let Q := bipartiteLift (centeredKernel T q)
  let M : Matrix (Sum Iota Iota) (Sum Iota Iota) Real := 1 + Q
  let R := Ring.inverse M
  let H := hamiltonianRepairProjection (Iota := Iota) q
  have hQ : Q.transpose = Q := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  have hM : M.transpose = M := by
    simp only [M, Matrix.transpose_add, Matrix.transpose_one, hQ]
  have hQNorm : norm Q <= rho :=
    le_trans (bipartiteLift_l2_norm_le (centeredKernel T q)) hNorm
  have hUnit : IsUnit M := by
    have hNeg : norm (-Q) < 1 := by
      rw [norm_neg]
      exact lt_of_le_of_lt hQNorm hRho
    simpa only [M, sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hNeg
  have hRM : R * M = 1 := Ring.inverse_mul_cancel _ hUnit
  have hMRT : M * R.transpose = 1 := by
    simpa only [Matrix.transpose_mul, hM, Matrix.transpose_one] using
      congrArg Matrix.transpose hRM
  have hR : R.transpose = R := by
    calc
      _ = (R * M) * R.transpose := by rw [hRM, one_mul]
      _ = R * (M * R.transpose) := mul_assoc _ _ _
      _ = R := by rw [hMRT, mul_one]
  have hH : H.transpose = H := by
    apply Matrix.ext
    intro i j
    simp only [H, Matrix.transpose_apply, hamiltonianRepairProjection]
    ring
  change (R - H).transpose = R - H
  rw [Matrix.transpose_sub, hR, hH]

theorem stochastic_repair_kernel_parity (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    hamiltonianRepairKernel T q * hamiltonianParityProjection q = 0 := by
  let B := centeredKernel T q
  let Q := bipartiteLift B
  let M : Matrix (Sum Iota Iota) (Sum Iota Iota) Real := 1 + Q
  let R := Ring.inverse M
  let H := hamiltonianRepairProjection (Iota := Iota) q
  let S := hamiltonianParityProjection (Iota := Iota) q
  have hBRow (i : Iota) : Finset.sum Finset.univ (fun j => B i j) = 0 := by
    change Finset.sum Finset.univ (fun j => T i j - q) = 0
    rw [Finset.sum_sub_distrib, hRow i, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hBCol (j : Iota) : Finset.sum Finset.univ (fun i => B i j) = 0 := by
    change Finset.sum Finset.univ (fun i => T i j - q) = 0
    rw [Finset.sum_sub_distrib, hCol j, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hQS : Q * S = 0 := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [Q, S, Matrix.mul_apply, Fintype.sum_sum_type, bipartiteLift,
        Matrix.fromBlocks, Matrix.transpose_apply, hamiltonianParityProjection,
        hamiltonianParitySign, mul_assoc, <- Finset.sum_mul, hBRow, hBCol]
  have hQNorm : norm Q <= rho := le_trans (bipartiteLift_l2_norm_le B) hNorm
  have hUnit : IsUnit M := by
    have hNeg : norm (-Q) < 1 := by
      rw [norm_neg]
      exact lt_of_le_of_lt hQNorm hRho
    simpa only [M, sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hNeg
  have hRM : R * M = 1 := Ring.inverse_mul_cancel _ hUnit
  have hMS : M * S = S := by
    dsimp only [M]
    rw [add_mul, one_mul, hQS, add_zero]
  have hRS : R * S = S := by
    calc
      _ = R * (M * S) := by rw [hMS]
      _ = (R * M) * S := (mul_assoc _ _ _).symm
      _ = S := by rw [hRM, one_mul]
  have hHS : H * S = S := by
    calc
      _ = HSMul.hSMul ((Fintype.card Iota : Real) * q) S := by
        apply Matrix.ext
        intro i j
        cases i <;> cases j <;>
          simp [H, S, Matrix.mul_apply, Fintype.sum_sum_type,
            hamiltonianRepairProjection, hamiltonianParityProjection,
            hamiltonianParitySign, Matrix.smul_apply, smul_eq_mul] <;> ring
      _ = S := by rw [hq, one_smul]
  change (R - H) * S = 0
  rw [sub_mul, hRS, hHS, sub_self]

theorem stochastic_parity_repair_kernel (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    hamiltonianParityProjection q * hamiltonianRepairKernel T q = 0 := by
  have hS : (hamiltonianParityProjection (Iota := Iota) q).transpose =
      hamiltonianParityProjection q := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.transpose_apply, hamiltonianParityProjection]
    ring
  have h := congrArg Matrix.transpose
    (stochastic_repair_kernel_parity T q rho hq hRow hCol hNorm hRho)
  simpa only [Matrix.transpose_mul, hS,
    stochastic_repair_kernel_transpose T q rho hNorm hRho, Matrix.transpose_zero] using h

end PrimeFactorOscillations
