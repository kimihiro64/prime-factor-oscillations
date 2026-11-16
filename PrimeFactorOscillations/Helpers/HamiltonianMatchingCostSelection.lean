/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianStochasticPeeling

/-! # A finite supported perfect matching with no larger linear cost -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianCrossCost (C P : Matrix Iota Iota Real) : Real :=
  Finset.univ.sum (fun i => Finset.univ.sum (fun j => C i j * P i j))

theorem hamiltonian_cross_cost_combination
    (C P Q : Matrix Iota Iota Real) (a b : Real) :
    hamiltonianCrossCost C (SMul.smul a P + SMul.smul b Q) =
      a * hamiltonianCrossCost C P + b * hamiltonianCrossCost C Q := by
  change Finset.univ.sum (fun i => Finset.univ.sum
    (fun j => C i j * (a * P i j + b * Q i j))) = _
  simp [hamiltonianCrossCost, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem hamiltonian_stochastic_unit_minimum
    (P : Matrix Iota Iota Real) (f : Equiv.Perm Iota)
    (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hEach : forall i, 1 <= P i (f i)) :
    P = hamiltonianPermutationCross f := by
  have hPerm := hamiltonian_permutation_cross_stochastic f
  have hNonneg (i j : Iota) : 0 <= P i j - hamiltonianPermutationCross f i j := by
    by_cases hij : j = f i
    . simp only [hamiltonianPermutationCross, hij, ite_true]
      exact sub_nonneg.mpr (hEach i)
    . simp only [hamiltonianPermutationCross, hij, ite_false, sub_zero]
      exact hP i j
  ext i j
  have hMass : Finset.univ.sum (fun j => P i j - hamiltonianPermutationCross f i j) = 0 := by
    rw [Finset.sum_sub_distrib, hRows, hPerm.2.1]
    ring
  have hPoint := Finset.single_le_sum (fun j _ => hNonneg i j) (Finset.mem_univ j)
  rw [hMass] at hPoint
  exact sub_eq_zero.mp (le_antisymm hPoint (hNonneg i j))

theorem hamiltonian_stochastic_matching_cost [Nonempty Iota]
    (C P : Matrix Iota Iota Real) (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i => P i j) = 1) :
    exists f : Equiv.Perm Iota, (forall i, 0 < P i (f i)) /\
      hamiltonianCrossCost C (hamiltonianPermutationCross f) <= hamiltonianCrossCost C P := by
  have hAux : forall n : Nat, forall R : Matrix Iota Iota Real,
      (hamiltonianPositiveCrossSupport R).card = n ->
      (forall i j, 0 <= R i j) ->
      (forall i, Finset.univ.sum (fun j => R i j) = 1) ->
      (forall j, Finset.univ.sum (fun i => R i j) = 1) ->
      exists f : Equiv.Perm Iota, (forall i, 0 < R i (f i)) /\
        hamiltonianCrossCost C (hamiltonianPermutationCross f) <= hamiltonianCrossCost C R := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro R hCount hR hRRows hRCols
      choose f hSupport using hamiltonian_stochastic_support_permutation R hR hRRows hRCols
      by_cases hGood :
          hamiltonianCrossCost C (hamiltonianPermutationCross f) <= hamiltonianCrossCost C R
      . exact Exists.intro f (And.intro hSupport hGood)
      . choose w hw0 hwLe hEach k hk using
          hamiltonian_stochastic_matched_minimum R f hR hRRows hSupport
        have hw1 : w < 1 := by
          by_contra h
          have hwEq : w = 1 := le_antisymm hwLe (le_of_not_gt h)
          have hUnit := hamiltonian_stochastic_unit_minimum R f hR hRRows
            (fun i => by simpa only [hwEq] using hEach i)
          exact hGood (by rw [hUnit])
        let T := hamiltonianStochasticPeel R f w
        have hPeel := hamiltonian_stochastic_peel_exact R f w k hR hRRows hRCols
          hw0 hw1 hEach hk
        have hLess : (hamiltonianPositiveCrossSupport T).card < n := by
          exact hPeel.2.2.2.1.trans_eq hCount
        choose g hgSupport hgCost using ih
          (hamiltonianPositiveCrossSupport T).card hLess T rfl
          hPeel.1 hPeel.2.1 hPeel.2.2.1
        have hDecomp : hamiltonianCrossCost C R =
            w * hamiltonianCrossCost C (hamiltonianPermutationCross f) +
              (1 - w) * hamiltonianCrossCost C T := by
          calc
            _ = hamiltonianCrossCost C
                (SMul.smul w (hamiltonianPermutationCross f) + SMul.smul (1 - w) T) :=
              congrArg (hamiltonianCrossCost C) hPeel.2.2.2.2
            _ = _ := hamiltonian_cross_cost_combination _ _ _ _ _
        have hTFraction : hamiltonianCrossCost C T <= hamiltonianCrossCost C R := by
          have hHigh := mul_pos hw0 (sub_pos.mpr (lt_of_not_ge hGood))
          have hSave : (1 - w) *
              (hamiltonianCrossCost C T - hamiltonianCrossCost C R) < 0 := by
            nlinarith only [hDecomp, hHigh]
          by_contra h
          have hBad := mul_pos (sub_pos.mpr hw1) (sub_pos.mpr (lt_of_not_ge h))
          linarith only [hSave, hBad]
        have hgOriginal (i : Iota) : 0 < R i (g i) := by
          have hPos := hgSupport i
          change 0 < (R i (g i) - w * hamiltonianPermutationCross f i (g i)) / (1 - w) at hPos
          have hNumerator := (div_pos_iff_of_pos_right (sub_pos.mpr hw1)).mp hPos
          have hW := mul_nonneg hw0.le
            ((hamiltonian_permutation_cross_stochastic f).1 i (g i))
          linarith only [hNumerator, hW]
        exact Exists.intro g (And.intro hgOriginal (hgCost.trans hTFraction))
  exact hAux _ P rfl hP hRows hCols

theorem hamiltonian_cross_cost_sub
    (C P Q : Matrix Iota Iota Real) :
    hamiltonianCrossCost C (P - Q) =
      hamiltonianCrossCost C P - hamiltonianCrossCost C Q := by
  simp [hamiltonianCrossCost, mul_sub, Finset.sum_sub_distrib]

theorem hamiltonian_stochastic_matching_nonpositive_direction [Nonempty Iota]
    (C P : Matrix Iota Iota Real) (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i => P i j) = 1) :
    exists f : Equiv.Perm Iota, (forall i, 0 < P i (f i)) /\
      hamiltonianCrossCost C (hamiltonianPermutationCross f - P) <= 0 := by
  choose f hSupport hCost using hamiltonian_stochastic_matching_cost C P hP hRows hCols
  refine Exists.intro f (And.intro hSupport ?_)
  rw [hamiltonian_cross_cost_sub]
  exact sub_nonpos.mpr hCost

end PrimeFactorOscillations
