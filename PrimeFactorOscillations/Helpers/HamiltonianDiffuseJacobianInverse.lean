/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDegreeJacobian
import PrimeFactorOscillations.Helpers.HamiltonianDiffuseRepairKernel
import PrimeFactorOscillations.Helpers.HamiltonianStochasticCompletion

/-! # The logarithmic compatible inverse of the actual degree Jacobian

The positive stochastic completion and its complete six-epsilon error
are consumed on the same matrix. The inverse acts on the original degree
Jacobian, with its parity projection intact and no added support edges.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianDiffuseInverseBudget (a rho : Real) : Real :=
  2 * (Real.log (2 * a) / (-Real.log rho) + 3) + 1 / (1 - rho)

theorem hamiltonian_diffuse_inverse_budget_positive (a rho : Real)
    (ha : 1 <= a) (hRho0 : 0 < rho) (hRho1 : rho < 1) :
    1 <= hamiltonianDiffuseInverseBudget a rho := by
  have hLog : 0 <= Real.log (2 * a) / (-Real.log rho) :=
    div_nonneg (Real.log_nonneg (by linarith only [ha]))
      (neg_pos.mpr (Real.log_neg hRho0 hRho1)).le
  have hInv : 0 < 1 / (1 - rho) := one_div_pos.mpr (sub_pos.mpr hRho1)
  unfold hamiltonianDiffuseInverseBudget
  linarith only [hLog, hInv]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_actual_diffuse_jacobian_inverse
    (T : Matrix Iota Iota Real) (q a eps rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hEps : 0 < eps) (hEpsSmall : eps <= 1 / 2)
    (hT : forall i j, 0 <= T i j)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps)
    (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho - 6 * eps)
    (hRho0 : 0 < rho) (hRho1 : rho < 1)
    (hSmall : 7 * eps * hamiltonianDiffuseInverseBudget (a + 9 * eps) rho <= 1 / 2) :
    exists G : Matrix (Sum Iota Iota) (Sum Iota Iota) Real,
      hamiltonianDegreeJacobian T * G = 1 - hamiltonianParityProjection q /\
      forall i, hamiltonianRowMass G i <=
        2 * hamiltonianDiffuseInverseBudget (a + 9 * eps) rho := by
  let U := hamiltonianStochasticCompletion T (1 + 2 * eps)
  let astar := a + 9 * eps
  let g := hamiltonianDiffuseInverseBudget astar rho
  let K := hamiltonianRepairKernel U q
  have hStar : 1 <= astar := by dsimp only [astar]; linarith only [ha, hEps]
  have hG : 1 <= g := hamiltonian_diffuse_inverse_budget_positive astar rho hStar hRho0 hRho1
  have hProb := hamiltonian_positive_stochastic_completion T eps hEps hT hRow hCol
  have hUNorm : norm (centeredKernel U q) <= rho := by
    have h := hamiltonian_stochastic_completion_centered_gap T eps q (rho - 6 * eps)
      hEps hEpsSmall hT hRow hCol hNorm
    exact h.trans_eq (by ring)
  have hm : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hqEq : q = 1 / (Fintype.card Iota : Real) := by
    field_simp [ne_of_gt hm]
    nlinarith only [hq]
  have hUpperDiv (i j : Iota) : T i j <= a / (Fintype.card Iota : Real) := by
    simpa only [hqEq, mul_one_div] using hUpper i j
  have hUUpper (i j : Iota) : U i j <= astar * q := by
    have h := hamiltonian_stochastic_completion_entry_bound T eps a hEps hRow hCol hUpperDiv i j
    have hDen : (Fintype.card Iota : Real) <=
        (1 + 2 * eps) * (Fintype.card Iota : Real) := by
      have hProduct := mul_nonneg hEps.le hm.le
      nlinarith only [hProduct]
    have hCompare := div_le_div_of_nonneg_left (lt_of_lt_of_le zero_lt_one hStar).le hm hDen
    rw [hqEq, mul_one_div]
    exact h.trans hCompare
  have hRight : (1 + bipartiteLift U) * K = 1 - hamiltonianParityProjection q :=
    stochastic_repair_kernel_right_inverse U q rho hq hProb.2.1 hProb.2.2 hUNorm hRho1
  have hK : forall i, hamiltonianRowMass K i <= g := by
    intro i
    have h := stochastic_repair_kernel_logarithmic_row U q astar rho hq hStar
      hProb.2.1 hProb.2.2 hProb.1 hUUpper hUNorm hRho0 hRho1 i
    have hGap : 0 < 1 - rho := sub_pos.mpr hRho1
    have hClear : (1 - rho) * g =
        2 * (1 - rho) * (Real.log (2 * astar) / (-Real.log rho) + 3) + 1 := by
      dsimp only [g, hamiltonianDiffuseInverseBudget]
      field_simp
    change (1 - rho) * hamiltonianRowMass K i <= _ at h
    rw [<- hClear] at h
    by_contra hNot
    have hStrict : g < hamiltonianRowMass K i := lt_of_not_ge hNot
    have hPositive := mul_pos hGap (sub_pos.mpr hStrict)
    nlinarith only [hPositive, h]
  have hPerturbSmall : (eps + 6 * eps) * g <= 1 / 2 := by
    change (eps + 6 * eps) * hamiltonianDiffuseInverseBudget astar rho <= _
    nlinarith only [hSmall]
  exact hamiltonian_degree_jacobian_inverse_from_reference T U K q eps (6 * eps) g
    hEps.le (by positivity) (zero_lt_one.le.trans hG)
    hProb.2.1 hProb.2.2 hRow hCol
    (hamiltonian_stochastic_completion_row_error T eps hEps hEpsSmall hT hRow hCol)
    (hamiltonian_stochastic_completion_col_error T eps hEps hEpsSmall hT hRow hCol)
    hRight hK hPerturbSmall

end PrimeFactorOscillations
