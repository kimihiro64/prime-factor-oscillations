/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Central
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceSignCube

/-! # Exact balanced sign-cube counts

Every coordinate cut is counted by the existing exact sign-cut
bijection. The central-binomial average gives the full polynomial
conditioning budget, including the smallest even dimensions.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hamiltonian_sign_cube_card :
    Fintype.card (I -> Bool) = 2 ^ Fintype.card I := by
  simp

theorem hamiltonian_sign_cut_filtered_count
    (P : Finset I -> Prop) [DecidablePred P] :
    (Finset.univ.filter (fun e : I -> Bool => P (hamiltonianSignCut e))).card =
      (Finset.univ.filter P).card := by
  have h := Equiv.sum_comp (hamiltonianSignCutEquiv (I := I))
    (fun D : Finset I => if P D then (1 : Nat) else 0)
  change Finset.univ.sum (fun e : I -> Bool => if P (hamiltonianSignCut e) then 1 else 0) =
    Finset.univ.sum (fun D : Finset I => if P D then 1 else 0) at h
  simpa only [Finset.sum_boole, Nat.cast_id] using h

def hamiltonianBalancedSigns (m : Nat) : Finset (I -> Bool) :=
  Finset.univ.filter (fun e => (hamiltonianSignCut e).card = m)

theorem hamiltonian_balanced_sign_count (m : Nat) :
    (hamiltonianBalancedSigns (I := I) m).card = (Fintype.card I).choose m := by
  have hSets : (Finset.univ.filter (fun D : Finset I => D.card = m)) =
      (Finset.univ : Finset I).powersetCard m := by
    ext D
    simp [Finset.mem_powersetCard]
  unfold hamiltonianBalancedSigns
  rw [hamiltonian_sign_cut_filtered_count (fun D : Finset I => D.card = m),
    hSets, Finset.card_powersetCard, Finset.card_univ]

theorem hamiltonian_central_binomial_mass (m : Nat) :
    2 ^ (2 * m) <= (2 * m + 1) * (2 * m).choose m := by
  have hSum := Finset.sum_le_sum (s := Finset.range (2 * m + 1))
    (fun r hr => Nat.choose_le_centralBinom r m)
  rw [Nat.sum_range_choose] at hSum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.centralBinom,
    Nat.cast_id] at hSum
  exact hSum

theorem hamiltonian_balanced_sign_mass (m : Nat) (hSize : Fintype.card I = 2 * m) :
    Fintype.card (I -> Bool) <=
      (Fintype.card I + 1) * (hamiltonianBalancedSigns (I := I) m).card := by
  rw [hamiltonian_sign_cube_card, hamiltonian_balanced_sign_count, hSize]
  exact hamiltonian_central_binomial_mass m

end PrimeFactorOscillations
