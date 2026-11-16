/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianForbiddenCrossPacket
import PrimeFactorOscillations.Helpers.HamiltonianForbiddenRepairBudgets

/-! # Full support-preserving repair after every small forbidden-edge deletion -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_bounded_mass_deletion_stochastic_repair
    (P Q : Matrix Iota Iota Real) (delta eta : Real)
    (hd0 : 0 < delta) (hd1 : delta < 1) (he : 0 <= eta)
    (hP : forall i j, 0 <= P i j)
    (hPRow : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCol : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hPGap : norm (centeredKernel P (1 / (Fintype.card Iota : Real))) <= 1 - delta)
    (hQ : forall i j, 0 <= Q i j) (hQP : forall i j, Q i j <= P i j)
    (hQRow : forall i, Finset.univ.sum (fun j => Q i j) <= eta)
    (hQCol : forall j, Finset.univ.sum (fun i => Q i j) <= eta)
    (hSmall : eta * Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
      hamiltonianForbiddenRepairSmall delta) :
    exists z : Sum Iota Iota -> Real,
      norm z <= hamiltonianNormalizedScalingCost delta * eta *
        Real.log (4 * (Fintype.card Iota : Real)) /\
      (forall i, 0 < 1 + z i) /\
      (forall i j, 0 <= hamiltonianScaledCross (P - Q) z i j) /\
      (forall i, Finset.univ.sum (fun j => hamiltonianScaledCross (P - Q) z i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => hamiltonianScaledCross (P - Q) z i j) = 1) /\
      (forall i j, hamiltonianScaledCross (P - Q) z i j = 0 <-> (P - Q) i j = 0) /\
      (forall i j, hamiltonianScaledCross (P - Q) z i j <= 2 * P i j) /\
      norm (hamiltonianScaledCross (P - Q) z - P) <=
        hamiltonianForbiddenRepairCost delta * eta *
          Real.log (4 * (Fintype.card Iota : Real)) /\
      norm (centeredKernel (hamiltonianScaledCross (P - Q) z)
        (1 / (Fintype.card Iota : Real))) <= 1 - delta / 2 := by
  let n : Real := Fintype.card Iota
  let q := 1 / n
  let L := Real.log (4 * n)
  let T := P - Q
  change norm (centeredKernel P q) <= 1 - delta at hPGap
  have hn : 1 <= n := by
    change (1 : Real) <= (Fintype.card Iota : Real)
    have hCard : 0 < Fintype.card Iota := Fintype.card_pos
    exact_mod_cast (show 1 <= Fintype.card Iota by omega)
  have hBudgets := hamiltonian_forbidden_repair_all_budgets n delta eta hn hd0 hd1 he hSmall
  have hT : forall i j, 0 <= T i j := fun i j => sub_nonneg.mpr (hQP i j)
  have hDegrees := hamiltonian_removed_cross_degree_packet P Q eta hPRow hPCol hQ hQRow hQCol
  have hQNorm := hamiltonian_removed_cross_mass_norm Q eta he hQ hQRow hQCol
  have hRaw : norm (centeredKernel T q) <= 1 - delta + 8 * eta := by
    have h := hamiltonian_removed_cross_centered_gap P Q q (1 - delta) eta hPGap hQNorm
    change norm (centeredKernel T q) <= 1 - delta + eta at h
    linarith only [h, he]
  choose z hz hPos hNonneg hRows hCols hSupport hCap hError using
    hamiltonian_centered_gap_stochastic_scaling T delta eta hd0 hd1 he hBudgets.1
      hT hDegrees.1 hDegrees.2 hRaw hBudgets.2.1
  let W := hamiltonianScaledCross T z
  have hDiff : T - P = -Q := by dsimp [T]; abel
  have hFullError : norm (W - P) <= hamiltonianForbiddenRepairCost delta * eta * L := by
    have hTriangle := norm_sub_le_norm_sub_add_norm_sub W T P
    rw [hDiff, norm_neg] at hTriangle
    have h := add_le_add hError hQNorm
    exact (hTriangle.trans h).trans hBudgets.2.2.1
  have hRemainingGap : norm (centeredKernel W q) <= 1 - delta / 2 := by
    have hTriangle := norm_sub_le_norm_sub_add_norm_sub W P
      (averagingKernel (Iota := Iota) q)
    change norm (centeredKernel W q) <= norm (W - P) + norm (centeredKernel P q) at hTriangle
    have hSave := hFullError.trans hBudgets.2.2.2
    linarith only [hTriangle, hSave, hPGap]
  refine Exists.intro z (And.intro hz (And.intro hPos (And.intro hNonneg
    (And.intro hRows (And.intro hCols (And.intro hSupport
      (And.intro ?_ (And.intro hFullError hRemainingGap))))))))
  intro i j
  have h := hCap i j
  change hamiltonianScaledCross T z i j <= 2 * P i j
  have hNonnegQ := hQ i j
  change hamiltonianScaledCross T z i j <= 2 * (P i j - Q i j) at h
  linarith only [h, hNonnegQ]

theorem hamiltonian_forbidden_edge_stochastic_repair
    (P : Matrix Iota Iota Real) (F : Finset (Prod Iota Iota)) (delta eta : Real)
    (hd0 : 0 < delta) (hd1 : delta < 1) (he : 0 <= eta)
    (hP : forall i j, 0 <= P i j)
    (hPRow : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCol : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hPGap : norm (centeredKernel P (1 / (Fintype.card Iota : Real))) <= 1 - delta)
    (hQRow : forall i, Finset.univ.sum (fun j => hamiltonianForbiddenCrossMatrix P F i j) <= eta)
    (hQCol : forall j, Finset.univ.sum (fun i => hamiltonianForbiddenCrossMatrix P F i j) <= eta)
    (hSmall : eta * Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
      hamiltonianForbiddenRepairSmall delta) :
    exists z : Sum Iota Iota -> Real,
      norm z <= hamiltonianNormalizedScalingCost delta * eta *
        Real.log (4 * (Fintype.card Iota : Real)) /\
      (forall i, 0 < 1 + z i) /\
      (forall i j, 0 <= hamiltonianScaledCross (P - hamiltonianForbiddenCrossMatrix P F) z i j) /\
      (forall i, Finset.univ.sum (fun j =>
        hamiltonianScaledCross (P - hamiltonianForbiddenCrossMatrix P F) z i j) = 1) /\
      (forall j, Finset.univ.sum (fun i =>
        hamiltonianScaledCross (P - hamiltonianForbiddenCrossMatrix P F) z i j) = 1) /\
      (forall i j, hamiltonianScaledCross (P - hamiltonianForbiddenCrossMatrix P F) z i j = 0 <->
        Or (P i j = 0) (Membership.mem F (i, j))) /\
      (forall i j, hamiltonianScaledCross (P - hamiltonianForbiddenCrossMatrix P F) z i j <=
        2 * P i j) /\
      norm (hamiltonianScaledCross (P - hamiltonianForbiddenCrossMatrix P F) z - P) <=
        hamiltonianForbiddenRepairCost delta * eta *
          Real.log (4 * (Fintype.card Iota : Real)) /\
      norm (centeredKernel (hamiltonianScaledCross (P - hamiltonianForbiddenCrossMatrix P F) z)
        (1 / (Fintype.card Iota : Real))) <= 1 - delta / 2 := by
  have hBounds := hamiltonian_forbidden_cross_mass_bounds P F hP
  choose z hz hPos hNonneg hRows hCols hSupport hCap hError hGap using
    hamiltonian_bounded_mass_deletion_stochastic_repair P (hamiltonianForbiddenCrossMatrix P F)
      delta eta hd0 hd1 he hP hPRow hPCol hPGap hBounds.1 hBounds.2 hQRow hQCol hSmall
  refine Exists.intro z (And.intro hz (And.intro hPos (And.intro hNonneg
    (And.intro hRows (And.intro hCols (And.intro ?_
      (And.intro hCap (And.intro hError hGap))))))))
  intro i j
  exact (hSupport i j).trans (hamiltonian_forbidden_cross_remaining_zero P F i j)

end PrimeFactorOscillations
