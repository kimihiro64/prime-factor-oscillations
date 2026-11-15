/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBoundaryEquations
import PrimeFactorOscillations.Helpers.HamiltonianDeletedSupportDefect
import PrimeFactorOscillations.Helpers.HamiltonianNonlinearRepair

/-! # The actual row defect and the full nonlinear scaling residual

The physical row degree is derived from the exact removed source.
The final identity matches the nonlinear fixed point to every retained
scaling equation, including its quadratic compensation.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonianDeletedSupportIndicator_disjSum
    (S U : Finset Iota) (i : Sum Iota Iota) :
    hamiltonianDeletedSupportIndicator S U i =
      if Membership.mem (S.disjSum U) i then 1 else 0 := by
  cases i <;>
    simp [hamiltonianDeletedSupportIndicator, Finset.inl_mem_disjSum,
      Finset.inr_mem_disjSum]

theorem hamiltonian_retained_row_defect
    (T : Matrix Iota Iota Real) (S U : Finset Iota)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota))) :
    ((bipartiteLift T).submatrix
      (fun j : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => j.val)
      (fun j : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => j.val)).mulVec 1 i =
        1 - hamiltonianDeletedSupportDefect T S U i.val := by
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let P := bipartiteLift T
  let ell := hamiltonianDeletedSupportDefect T S U
  let u := hamiltonianDeletedSupportIndicator S U
  have hU (d : D) : u d.val = 1 := by
    dsimp only [u]
    rw [hamiltonianDeletedSupportIndicator_disjSum]
    exact if_pos d.property
  have hR (j : R) : u j.val = 0 := by
    dsimp only [u]
    rw [hamiltonianDeletedSupportIndicator_disjSum]
    exact if_neg (Finset.mem_compl.mp j.property)
  have hRemoved : ell i.val =
      Finset.sum Finset.univ (fun d : D => P i.val d.val) := by
    have hEll := congrArg (fun f => f i.val)
      (hamiltonianDeletedSupportDefect_eq_mulVec T S U)
    change ell i.val = P.mulVec u i.val at hEll
    have hPart := hamiltonian_sum_support_partition (fun k => P i.val k * u k) D
    simp only [hU, hR, mul_one, mul_zero, Finset.sum_const_zero, add_zero] at hPart
    exact hEll.trans hPart
  have hPRow (k : Sum Iota Iota) : Finset.sum Finset.univ (fun j => P k j) = 1 := by
    cases k with
    | inl k =>
      simpa [P, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type] using hRow k
    | inr k =>
      simpa [P, bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply,
        Fintype.sum_sum_type] using hCol k
  have hPart := hamiltonian_sum_support_partition (fun k => P i.val k) D
  rw [hPRow i.val, <- hRemoved] at hPart
  change Finset.sum Finset.univ (fun j : R => P i.val j.val * 1) = 1 - ell i.val
  simp only [mul_one]
  linarith only [hPart]

theorem hamiltonian_nonlinear_scaling_residual
    (P : Matrix Iota Iota Real) (ell z : Iota -> Real)
    (hDegree : forall i, P.mulVec 1 i = 1 - ell i) (i : Iota) :
    (1 + z i) * P.mulVec (1 + z) i - 1 =
      ((1 : Matrix Iota Iota Real) + P).mulVec z i -
        (ell + hamiltonianRepairNonlinear P ell z) i := by
  rw [Matrix.mulVec_add, Matrix.add_mulVec, Matrix.one_mulVec]
  simp only [Pi.add_apply]
  rw [hDegree i]
  change (1 + z i) * ((1 - ell i) + P.mulVec z i) - 1 =
    z i + P.mulVec z i - (ell i + (ell i * z i - z i * P.mulVec z i))
  ring

end PrimeFactorOscillations
