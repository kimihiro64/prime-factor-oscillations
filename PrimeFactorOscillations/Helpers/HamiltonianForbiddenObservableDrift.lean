/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianForbiddenEdgeRepair
import PrimeFactorOscillations.Helpers.HamiltonianScaledCrossMass

/-! # One repaired stochastic witness controls every row and column observable -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianForbiddenObservableCost (delta : Real) : Real :=
  3 * hamiltonianNormalizedScalingCost delta + 1 / Real.log 4

theorem hamiltonian_forbidden_observable_constant_positive
    (delta : Real) (hd0 : 0 < delta) (hd1 : delta < 1) :
    0 < hamiltonianForbiddenObservableCost delta := by
  have hBase := (hamiltonian_normalized_scaling_constants_positive delta hd0 hd1).2
  have hFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold hamiltonianForbiddenObservableCost
  positivity

theorem hamiltonian_forbidden_observable_budget
    (n delta eta : Real) (hn : 1 <= n)
    (hd0 : 0 < delta) (hd1 : delta < 1) (he : 0 <= eta)
    (hSmall : eta * Real.log (4 * n) ^ 2 <= hamiltonianForbiddenRepairSmall delta) :
    let r := hamiltonianNormalizedScalingCost delta * eta * Real.log (4 * n)
    0 <= r /\ r <= 1 /\
      eta + (2 * r + r ^ 2) <=
        hamiltonianForbiddenObservableCost delta * eta * Real.log (4 * n) := by
  let L := Real.log (4 * n)
  let r := hamiltonianNormalizedScalingCost delta * eta * L
  have hFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hL : Real.log 4 <= L :=
    Real.log_le_log (by norm_num) (by linarith only [hn])
  have hL0 : 0 <= L := hFour.le.trans hL
  have hC := (hamiltonian_normalized_scaling_constants_positive delta hd0 hd1).2
  have hr : 0 <= r := mul_nonneg (mul_nonneg hC.le he) hL0
  have hB := hamiltonian_forbidden_repair_all_budgets n delta eta hn hd0 hd1 he hSmall
  have hrSmall : r <= 1 := by
    have hFull := hB.2.2.1.trans hB.2.2.2
    change r + eta <= delta / 2 at hFull
    linarith only [hFull, he, hd1]
  have hSq : r ^ 2 <= r := by nlinarith only [hr, hrSmall]
  have hAbsorb := mul_le_mul_of_nonneg_left hL (div_nonneg he hFour.le)
  have hCancel : (eta / Real.log 4) * Real.log 4 = eta := by
    field_simp [ne_of_gt hFour]
  rw [hCancel] at hAbsorb
  refine And.intro hr (And.intro hrSmall ?_)
  calc
    eta + (2 * r + r ^ 2) <= (eta / Real.log 4) * L + 3 * r := by
      linarith only [hAbsorb, hSq]
    _ = hamiltonianForbiddenObservableCost delta * eta * Real.log (4 * n) := by
      dsimp [r, L, hamiltonianForbiddenObservableCost]
      ring

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_bounded_mass_deletion_repair_observables
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
      (norm z <= hamiltonianNormalizedScalingCost delta * eta *
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
        (1 / (Fintype.card Iota : Real))) <= 1 - delta / 2) /\
      (forall i, Finset.univ.sum
        (fun j => abs (hamiltonianScaledCross (P - Q) z i j - P i j)) <=
          hamiltonianForbiddenObservableCost delta * eta *
            Real.log (4 * (Fintype.card Iota : Real))) /\
      (forall j, Finset.univ.sum
        (fun i => abs (hamiltonianScaledCross (P - Q) z i j - P i j)) <=
          hamiltonianForbiddenObservableCost delta * eta *
            Real.log (4 * (Fintype.card Iota : Real))) /\
      forall S : Finset Iota,
        (forall i, abs (S.sum (fun j =>
          hamiltonianScaledCross (P - Q) z i j - P i j)) <=
            hamiltonianForbiddenObservableCost delta * eta *
              Real.log (4 * (Fintype.card Iota : Real))) /\
        (forall j, abs (S.sum (fun i =>
          hamiltonianScaledCross (P - Q) z i j - P i j)) <=
            hamiltonianForbiddenObservableCost delta * eta *
              Real.log (4 * (Fintype.card Iota : Real))) := by
  choose z hSpec using hamiltonian_bounded_mass_deletion_stochastic_repair P Q delta eta
    hd0 hd1 he hP hPRow hPCol hPGap hQ hQP hQRow hQCol hSmall
  let n : Real := Fintype.card Iota
  let r := hamiltonianNormalizedScalingCost delta * eta * Real.log (4 * n)
  let b := hamiltonianForbiddenObservableCost delta * eta * Real.log (4 * n)
  have hn : 1 <= n := by
    change (1 : Real) <= (Fintype.card Iota : Real)
    have hCard : 0 < Fintype.card Iota := Fintype.card_pos
    exact_mod_cast (show 1 <= Fintype.card Iota by omega)
  have hB := hamiltonian_forbidden_observable_budget n delta eta hn hd0 hd1 he hSmall
  have hZ : forall k, abs (z k) <= r :=
    (pi_norm_le_iff_of_nonneg hB.1).mp hSpec.1
  have hMass := hamiltonian_scaled_deletion_absolute_mass P Q z r eta hB.1 hZ
    hPRow hPCol hQ hQP hQRow hQCol
  have hRows (i : Iota) : Finset.univ.sum
      (fun j => abs (hamiltonianScaledCross (P - Q) z i j - P i j)) <= b :=
    (hMass.1 i).trans hB.2.2
  have hCols (j : Iota) : Finset.univ.sum
      (fun i => abs (hamiltonianScaledCross (P - Q) z i j - P i j)) <= b :=
    (hMass.2 j).trans hB.2.2
  refine Exists.intro z (And.intro hSpec (And.intro hRows (And.intro hCols ?_)))
  intro S
  exact hamiltonian_absolute_mass_subset_observables
    (hamiltonianScaledCross (P - Q) z - P) b hRows hCols S

end PrimeFactorOscillations
