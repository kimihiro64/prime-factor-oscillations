/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFiniteRowInverse
import PrimeFactorOscillations.Helpers.HamiltonianRepairKernel

/-! # Uniform invertibility of the actual deleted-coordinate block

The deleted supports are arbitrary. The proof uses the full repair kernel,
and includes the empty support without imposing a nonempty subtype.
This inverse controls the boundary Schur correction in the minor expansion.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_deleted_block_inverse
    (T : Matrix Iota Iota Real) (D : Finset (Sum Iota Iota)) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (D.card : Real) * (4 * a * q) <= (1 - rho) / 2) :
    IsUnit ((hamiltonianRepairKernel T q).submatrix
      (fun i : D => i.val) (fun j : D => j.val)) /\
    forall i : D, Finset.sum Finset.univ
      (fun j : D => abs (Ring.inverse ((hamiltonianRepairKernel T q).submatrix
        (fun k : D => k.val) (fun k : D => k.val)) i j)) <= 2 := by
  let M := (hamiltonianRepairKernel T q).submatrix
    (fun i : D => i.val) (fun j : D => j.val)
  apply matrix_row_half_inverse M
  intro i
  have hEntry (j : D) : (1 - rho) * abs ((M - 1) i j) <= 4 * a * q := by
    have h := stochastic_repair_kernel_entry T q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho i.val j.val
    simpa only [M, Matrix.sub_apply, Matrix.submatrix_apply,
      Matrix.one_apply, Subtype.ext_iff] using h
  have hSum : (1 - rho) * Finset.sum Finset.univ
      (fun j : D => abs ((M - 1) i j)) <= (D.card : Real) * (4 * a * q) := by
    rw [Finset.mul_sum]
    calc
      _ <= Finset.sum Finset.univ (fun _ : D => 4 * a * q) :=
        Finset.sum_le_sum (fun j _ => hEntry j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_coe, nsmul_eq_mul]
  have hGap : 0 < 1 - rho := sub_pos.mpr hRho
  nlinarith only [hSum, hSmall, hGap]

end PrimeFactorOscillations
