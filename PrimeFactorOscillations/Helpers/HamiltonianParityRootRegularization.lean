/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorQuadraticCompensation

/-! # Actual regularization of the singular parity root

The parity direction is retained as its exact rank-one projection.
The determinant factor is cleared before any occupancy moment estimate.
These identities supply the nonsingular matrix used to compute the
signed one- and two-coordinate moments.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianParityRegularizedKernel (T : Matrix Iota Iota Real) (q tau : Real) :
    Matrix (Sum Iota Iota) (Sum Iota Iota) Real :=
  1 + bipartiteLift T + hamiltonianParityProjection q -
    HSMul.hSMul tau (bipartiteLift T)

theorem hamiltonian_parity_projection_idempotent (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) :
    hamiltonianParityProjection (Iota := Iota) q * hamiltonianParityProjection q =
      hamiltonianParityProjection q := by
  have hQQ : (Fintype.card Iota : Real) * q ^ 2 = q := by
    have h := congrArg (fun x : Real => x * q) hq
    nlinarith only [h]
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hamiltonianParityProjection,
      hamiltonianParitySign] <;> nlinarith only [hQQ]

theorem hamiltonian_parity_projection_det (q c : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) :
    Matrix.det ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
      HSMul.hSMul c (hamiltonianParityProjection q)) = 1 + c := by
  have hOuter :
      (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
          HSMul.hSMul c (hamiltonianParityProjection q) =
        1 + Matrix.replicateCol PUnit.{1}
          (fun i : Sum Iota Iota => c * q / 2 * hamiltonianParitySign i) *
            Matrix.replicateRow PUnit.{1} (hamiltonianParitySign (Iota := Iota)) := by
    apply Matrix.ext
    intro i j
    simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow,
      Matrix.smul_apply, smul_eq_mul, hamiltonianParityProjection]
    ring
  rw [hOuter, @Matrix.det_one_add_replicateCol_mul_replicateRow
    (Sum Iota Iota) Real _ _ _ PUnit.{1} _
      (fun i : Sum Iota Iota => c * q / 2 * hamiltonianParitySign i)
        (hamiltonianParitySign (Iota := Iota))]
  have hSum : Finset.univ.sum (fun i : Sum Iota Iota =>
      hamiltonianParitySign i * (c * q / 2 * hamiltonianParitySign i)) = c := by
    simp only [Fintype.sum_sum_type, hamiltonianParitySign, one_mul, mul_one,
      neg_mul, mul_neg, neg_neg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ = c * ((Fintype.card Iota : Real) * q) := by ring
      _ = c := by rw [hq, mul_one]
  change 1 + Finset.univ.sum (fun i : Sum Iota Iota =>
    hamiltonianParitySign i * (c * q / 2 * hamiltonianParitySign i)) = 1 + c
  rw [hSum]

variable [Nonempty Iota]

theorem stochastic_kernel_mul_parity (T : Matrix Iota Iota Real) (q : Real)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    bipartiteLift T * hamiltonianParityProjection q = -hamiltonianParityProjection q := by
  have h := congrArg Matrix.transpose (stochastic_parity_projection_mul_kernel T q hRow hCol)
  have hP : (bipartiteLift T).transpose = bipartiteLift T := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  have hS : (hamiltonianParityProjection (Iota := Iota) q).transpose =
      hamiltonianParityProjection q := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.transpose_apply, hamiltonianParityProjection]
    ring
  simpa only [Matrix.transpose_mul, Matrix.transpose_neg, hP, hS] using h

theorem stochastic_regularized_parity_eigen (T : Matrix Iota Iota Real)
    (q tau : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    hamiltonianParityRegularizedKernel T q tau * hamiltonianParityProjection q =
      HSMul.hSMul (1 + tau) (hamiltonianParityProjection q) := by
  have hP := stochastic_kernel_mul_parity T q hRow hCol
  have hS := hamiltonian_parity_projection_idempotent (Iota := Iota) q hq
  dsimp only [hamiltonianParityRegularizedKernel]
  simp only [sub_mul, add_mul, one_mul, Matrix.smul_mul, hP, hS]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem stochastic_parity_regularization_factor (T : Matrix Iota Iota Real)
    (q tau : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hTau : Not (1 + tau = 0)) :
    hamiltonianParityRegularizedKernel T q tau *
        ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
          HSMul.hSMul (-(1 / (1 + tau))) (hamiltonianParityProjection q)) =
      1 + HSMul.hSMul (1 - tau) (bipartiteLift T) := by
  rw [mul_add, mul_one, Matrix.mul_smul,
    stochastic_regularized_parity_eigen T q tau hq hRow hCol, smul_smul]
  have hScalar : -(1 / (1 + tau)) * (1 + tau) = -1 := by field_simp [hTau]
  rw [hScalar]
  apply Matrix.ext
  intro i j
  simp only [hamiltonianParityRegularizedKernel, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem stochastic_parity_regularization_det (T : Matrix Iota Iota Real)
    (q tau : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hTau : Not (1 + tau = 0)) :
    Matrix.det ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
      HSMul.hSMul (1 - tau) (bipartiteLift T)) =
        tau / (1 + tau) * Matrix.det (hamiltonianParityRegularizedKernel T q tau) := by
  rw [<- stochastic_parity_regularization_factor T q tau hq hRow hCol hTau, Matrix.det_mul,
    hamiltonian_parity_projection_det q (-(1 / (1 + tau))) hq]
  have hScalar : 1 + -(1 / (1 + tau)) = tau / (1 + tau) := by field_simp [hTau]; ring
  rw [hScalar, mul_comm]

theorem stochastic_regularized_kernel_inverse (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    IsUnit (hamiltonianParityRegularizedKernel T q 0) /\
    Ring.inverse (hamiltonianParityRegularizedKernel T q 0) =
      hamiltonianRepairKernel T q + hamiltonianParityProjection q := by
  let P := bipartiteLift T
  let S := hamiltonianParityProjection (Iota := Iota) q
  let K := hamiltonianRepairKernel T q
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + P
  let M := H + S
  have hM : hamiltonianParityRegularizedKernel T q 0 = M := by
    simp only [hamiltonianParityRegularizedKernel, zero_smul, sub_zero, M, H, P, S]
  have hHK : H * K = 1 - S :=
    stochastic_repair_kernel_right_inverse T q rho hq hRow hCol hNorm hRho
  have hHS : H * S = 0 := by
    dsimp only [H]
    rw [add_mul, one_mul, stochastic_kernel_mul_parity T q hRow hCol, add_neg_cancel]
  have hSK : S * K = 0 :=
    stochastic_parity_repair_kernel T q rho hq hRow hCol hNorm hRho
  have hSS : S * S = S := hamiltonian_parity_projection_idempotent q hq
  have hProduct : M * (K + S) = 1 := by
    dsimp only [M]
    rw [add_mul, mul_add, mul_add, hHK, hHS, hSK, hSS, add_zero, zero_add, sub_add_cancel]
  have hOther : (K + S) * M = 1 := _root_.mul_eq_one_comm.mp hProduct
  have hUnit : IsUnit M := by
    refine Exists.intro
      ({ val := M, inv := K + S, val_inv := hProduct, inv_val := hOther } :
        Units (Matrix (Sum Iota Iota) (Sum Iota Iota) Real)) ?_
    rfl
  have hInverse : Ring.inverse M = K + S := by
    calc
      _ = ((K + S) * M) * Ring.inverse M := by rw [hOther, one_mul]
      _ = (K + S) * (M * Ring.inverse M) := mul_assoc _ _ _
      _ = _ := by rw [Ring.mul_inverse_cancel _ hUnit, mul_one]
  rw [hM]
  exact And.intro hUnit hInverse

end PrimeFactorOscillations
