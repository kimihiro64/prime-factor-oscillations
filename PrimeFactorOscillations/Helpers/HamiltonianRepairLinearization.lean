/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDeletedSupportDefect
import PrimeFactorOscillations.Helpers.HamiltonianRepairInverse

/-! # Exact full linearized repair for the actual deleted supports

Equal support cardinalities give exact parity compatibility of the
actual defect. The parity-corrected inverse therefore solves the full
linearized system, alongside the independent nine-times-size bound.
The boundary and nonlinear scaling corrections are handled separately.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonianDeletedSupportDefect_parity
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q : Real)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1) :
    (hamiltonianParityProjection q).mulVec (hamiltonianDeletedSupportDefect T S U) =
      (0 : Sum Iota Iota -> Real) := by
  have hMasses := hamiltonianDeletedSupportDefect_half_masses T S U hRow hCol
  apply funext
  intro i
  cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      hamiltonianParityProjection, hamiltonianParitySign,
      <- Finset.mul_sum, hMasses.1, hMasses.2, hCard] <;> ring

variable [Nonempty Iota]

theorem stochastic_deleted_support_linear_equation
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + bipartiteLift T).mulVec
        ((hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U)) =
      hamiltonianDeletedSupportDefect T S U := by
  rw [Matrix.mulVec_mulVec,
    stochastic_repair_kernel_right_inverse T q rho hq hRow hCol hNorm hRho,
    Matrix.sub_mulVec, Matrix.one_mulVec,
    hamiltonianDeletedSupportDefect_parity T S U hCard q hRow hCol, sub_zero]

end PrimeFactorOscillations
