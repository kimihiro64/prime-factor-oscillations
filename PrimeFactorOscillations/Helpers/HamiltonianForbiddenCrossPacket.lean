/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianNormalizedScaling

/-! # Exact forbidden cross-edge masses and the remaining centered packet -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianForbiddenCrossMatrix (P : Matrix Iota Iota Real)
    (F : Finset (Prod Iota Iota)) : Matrix Iota Iota Real :=
  fun i j => if Membership.mem F (i, j) then P i j else 0

theorem hamiltonian_forbidden_cross_mass_bounds (P : Matrix Iota Iota Real)
    (F : Finset (Prod Iota Iota)) (hP : forall i j, 0 <= P i j) :
    (forall i j, 0 <= hamiltonianForbiddenCrossMatrix P F i j) /\
      (forall i j, hamiltonianForbiddenCrossMatrix P F i j <= P i j) := by
  have hEach (i j : Iota) : 0 <= hamiltonianForbiddenCrossMatrix P F i j /\
      hamiltonianForbiddenCrossMatrix P F i j <= P i j := by
    by_cases h : Membership.mem F (i, j)
    case pos =>
      simp only [hamiltonianForbiddenCrossMatrix, h, ite_true]
      exact And.intro (hP i j) (le_refl _)
    case neg =>
      simp only [hamiltonianForbiddenCrossMatrix, h, ite_false]
      exact And.intro (le_refl _) (hP i j)
  exact And.intro (fun i j => (hEach i j).1) (fun i j => (hEach i j).2)

theorem hamiltonian_removed_cross_mass_norm
    (Q : Matrix Iota Iota Real) (eta : Real) (he : 0 <= eta)
    (hQ : forall i j, 0 <= Q i j)
    (hRow : forall i, Finset.univ.sum (fun j => Q i j) <= eta)
    (hCol : forall j, Finset.univ.sum (fun i => Q i j) <= eta) :
    norm Q <= eta := by
  apply hamiltonian_l2_row_column_budget Q eta he
  . intro i
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hQ i _)] using hRow i
  . intro j
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hQ _ j)] using hCol j

theorem hamiltonian_removed_cross_degree_packet
    (P Q : Matrix Iota Iota Real) (eta : Real)
    (hPRow : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCol : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hQ : forall i j, 0 <= Q i j)
    (hQRow : forall i, Finset.univ.sum (fun j => Q i j) <= eta)
    (hQCol : forall j, Finset.univ.sum (fun i => Q i j) <= eta) :
    (forall i, abs (hamiltonianCrossRowDegrees (P - Q) i - 1) <= eta) /\
      (forall j, abs (hamiltonianCrossColumnDegrees (P - Q) j - 1) <= eta) := by
  constructor
  . intro i
    change abs (Finset.univ.sum (fun j => P i j - Q i j) - 1) <= eta
    rw [Finset.sum_sub_distrib, hPRow i]
    have hN : 0 <= Finset.univ.sum (fun j => Q i j) :=
      Finset.sum_nonneg (fun j _ => hQ i j)
    have hId : 1 - Finset.univ.sum (fun j => Q i j) - 1 =
      -(Finset.univ.sum (fun j => Q i j)) := by ring
    rw [hId, abs_neg, abs_of_nonneg hN]
    exact hQRow i
  . intro j
    change abs (Finset.univ.sum (fun i => P i j - Q i j) - 1) <= eta
    rw [Finset.sum_sub_distrib, hPCol j]
    have hN : 0 <= Finset.univ.sum (fun i => Q i j) :=
      Finset.sum_nonneg (fun i _ => hQ i j)
    have hId : 1 - Finset.univ.sum (fun i => Q i j) - 1 =
      -(Finset.univ.sum (fun i => Q i j)) := by ring
    rw [hId, abs_neg, abs_of_nonneg hN]
    exact hQCol j

theorem hamiltonian_removed_cross_centered_gap
    (P Q : Matrix Iota Iota Real) (q rho eta : Real)
    (hP : norm (centeredKernel P q) <= rho) (hQ : norm Q <= eta) :
    norm (centeredKernel (P - Q) q) <= rho + eta := by
  have hId : centeredKernel (P - Q) q = centeredKernel P q - Q := by
    unfold centeredKernel
    abel
  rw [hId]
  exact (norm_sub_le _ _).trans (add_le_add hP hQ)

theorem hamiltonian_forbidden_cross_remaining_zero
    (P : Matrix Iota Iota Real) (F : Finset (Prod Iota Iota)) (i j : Iota) :
    (P - hamiltonianForbiddenCrossMatrix P F) i j = 0 <->
      Or (P i j = 0) (Membership.mem F (i, j)) := by
  change P i j - (if Membership.mem F (i, j) then P i j else 0) = 0 <->
    Or (P i j = 0) (Membership.mem F (i, j))
  by_cases h : Membership.mem F (i, j) <;> simp [h]

end PrimeFactorOscillations
