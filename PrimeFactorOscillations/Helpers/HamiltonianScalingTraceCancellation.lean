/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceBoundaryInverse
import PrimeFactorOscillations.Helpers.HamiltonianScalingPerturbation

/-! # Exact full signed scaling trace and centering cancellation

All linear scaling terms are evaluated on the complete stochastic
matrix before removed-coordinate or Schur remainders are bounded.
The rank-centering trace vanishes exactly.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_full_scaling_trace_cancellation
    (T : Matrix Iota Iota Real) (q rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    let P := bipartiteLift T
    let C := bipartiteLift (fun _ _ : Iota => (1 : Real))
    let Omega := bipartiteLift (centeredKernel T q)
    let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
    let R := Ring.inverse H
    let Gamma := Omega * R
    R * C = C /\
    C * R = C /\
    P * R = Gamma + HSMul.hSMul q C /\
    R * P = Gamma + HSMul.hSMul q C /\
    Matrix.trace (R * C) = 0 /\
    forall z : Sum Iota Iota -> Real,
      Matrix.trace (R * (Matrix.diagonal z * P + P * Matrix.diagonal z)) =
        2 * Finset.sum Finset.univ (fun i => Gamma i i * z i) := by
  let B := centeredKernel T q
  let P := bipartiteLift T
  let C := bipartiteLift (fun _ _ : Iota => (1 : Real))
  let Omega := bipartiteLift B
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
  let R := Ring.inverse H
  let Gamma := Omega * R
  have hBRow (i : Iota) : Finset.sum Finset.univ (fun j => B i j) = 0 := by
    change Finset.sum Finset.univ (fun j => T i j - q) = 0
    rw [Finset.sum_sub_distrib, hRow i, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hBCol (j : Iota) : Finset.sum Finset.univ (fun i => B i j) = 0 := by
    change Finset.sum Finset.univ (fun i => T i j - q) = 0
    rw [Finset.sum_sub_distrib, hCol j, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hOC : Omega * C = 0 := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [Omega, C, Matrix.mul_apply, Fintype.sum_sum_type, bipartiteLift,
        Matrix.fromBlocks, Matrix.transpose, hBRow, hBCol]
  have hCO : C * Omega = 0 := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [Omega, C, Matrix.mul_apply, Fintype.sum_sum_type, bipartiteLift,
        Matrix.fromBlocks, Matrix.transpose, hBRow, hBCol]
  have hP : P = Omega + HSMul.hSMul q C := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [P, Omega, B, C, bipartiteLift, Matrix.fromBlocks, Matrix.transpose,
        centeredKernel, averagingKernel, Matrix.smul_apply, smul_eq_mul]
  have hUnit : IsUnit H := by
    have hOmegaNorm : norm Omega <= rho :=
      le_trans (bipartiteLift_l2_norm_le _) hNorm
    have hNeg : norm (-Omega) < 1 := by rw [norm_neg]; exact lt_of_le_of_lt hOmegaNorm hRho
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hNeg
  have hHR : H * R = 1 := Ring.mul_inverse_cancel _ hUnit
  have hRH : R * H = 1 := Ring.inverse_mul_cancel _ hUnit
  have hHC : H * C = C := by
    change (1 + Omega) * C = C
    rw [add_mul, one_mul, hOC, add_zero]
  have hCH : C * H = C := by
    change C * (1 + Omega) = C
    rw [mul_add, mul_one, hCO, add_zero]
  have hRC : R * C = C := by
    calc
      _ = R * (H * C) := by rw [hHC]
      _ = (R * H) * C := (mul_assoc _ _ _).symm
      _ = _ := by rw [hRH, one_mul]
  have hCR : C * R = C := by
    calc
      _ = (C * H) * R := by rw [hCH]
      _ = C * (H * R) := mul_assoc _ _ _
      _ = _ := by rw [hHR, mul_one]
  have hRO : R * Omega = Gamma := by
    have hLeft : R + R * Omega = 1 := by
      simpa only [H, mul_add, mul_one] using hRH
    have hRight : R + Omega * R = 1 := by
      simpa only [H, add_mul, one_mul] using hHR
    exact add_left_cancel (hLeft.trans hRight.symm)
  have hPR : P * R = Gamma + HSMul.hSMul q C := by
    rw [hP, add_mul, Matrix.smul_mul, hCR]
  have hRP : R * P = Gamma + HSMul.hSMul q C := by
    rw [hP, mul_add, Matrix.mul_smul, hRC, hRO]
  have hDiag (i : Sum Iota Iota) : C i i = 0 := by cases i <;> rfl
  have hTraceC : Matrix.trace (R * C) = 0 := by
    rw [hRC]
    exact Finset.sum_eq_zero (fun i _ => hDiag i)
  refine And.intro hRC (And.intro hCR (And.intro hPR (And.intro hRP (And.intro hTraceC ?_))))
  intro z
  let Z := Matrix.diagonal z
  have hRead (A : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) :
      Matrix.trace (A * Z) = Finset.sum Finset.univ (fun i => A i i * z i) := by
    simp only [Matrix.trace, Matrix.diag_apply, Z, Matrix.mul_diagonal]
  have hFirst : Matrix.trace (R * (Z * P)) = Matrix.trace ((P * R) * Z) := by
    calc
      _ = Matrix.trace ((R * Z) * P) := congrArg Matrix.trace (mul_assoc _ _ _).symm
      _ = Matrix.trace (P * (R * Z)) := Matrix.trace_mul_comm _ _
      _ = _ := congrArg Matrix.trace (mul_assoc _ _ _).symm
  change Matrix.trace (R * (Z * P + P * Z)) = _
  rw [mul_add, Matrix.trace_add, hFirst, <- mul_assoc, hRead, hRead, hPR, hRP]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hDiag, mul_zero, add_zero]
  ring

end PrimeFactorOscillations
