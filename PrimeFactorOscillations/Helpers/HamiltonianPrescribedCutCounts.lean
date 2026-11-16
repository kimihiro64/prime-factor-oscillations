/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBalancedCutCounts

/-! # Exact balanced cuts with two prescribed distinct coordinates

Insertion and deletion give a genuine finite bijection, retaining
both endpoint constraints. The smallest even dimension is included
in the full polynomial conditioning budget.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hamiltonian_prescribed_powerset_count
    (S : Finset I) (a : I) (ha : Membership.mem S a) (m : Nat) :
    ((S.powersetCard (m + 1)).filter (fun D => Membership.mem D a)).card =
      (S.erase a).card.choose m := by
  classical
  let B := (S.erase a).powersetCard m
  let C := (S.powersetCard (m + 1)).filter (fun D => Membership.mem D a)
  let g := fun (D : Finset I) (_ : Membership.mem B D) =>
    (Insert.insert a D : Finset I)
  have hNoA (D : Finset I) (hD : Membership.mem B D) : Not (Membership.mem D a) := by
    intro h
    have hx := (Finset.mem_powersetCard.mp hD).1 h
    simp at hx
  have hTo (D : Finset I) (hD : Membership.mem B D) : Membership.mem C (g D hD) := by
    have hSub := (Finset.mem_powersetCard.mp hD).1
    have hCard := (Finset.mem_powersetCard.mp hD).2
    have hInsertSub : (Insert.insert a D : Finset I) <= S := by
      intro i hi
      have hCases := Finset.mem_insert.mp hi
      exact hCases.elim (fun hia => by rw [hia]; exact ha)
        (fun hiD => Finset.mem_of_mem_erase (hSub hiD))
    have hInsertCard : (Insert.insert a D : Finset I).card = m + 1 := by
      simp [hNoA D hD, hCard]
    apply Finset.mem_filter.mpr
    exact And.intro (Finset.mem_powersetCard.mpr (And.intro hInsertSub hInsertCard))
      (by simp [g])
  have hInj (D : Finset I) (hD : Membership.mem B D)
      (T : Finset I) (hT : Membership.mem B T) (h : g D hD = g T hT) : D = T := by
    have hx := congrArg (fun U : Finset I => U.erase a) h
    dsimp only [g] at hx
    rw [Finset.erase_insert (hNoA D hD), Finset.erase_insert (hNoA T hT)] at hx
    exact hx
  have hOnto (T : Finset I) (hT : Membership.mem C T) :
      Exists (fun D => Exists (fun hD : Membership.mem B D => g D hD = T)) := by
    have hPower := (Finset.mem_filter.mp hT).1
    have hTa := (Finset.mem_filter.mp hT).2
    let D := T.erase a
    have hSub : D <= S.erase a := by
      intro i hi
      have hMem := Finset.mem_erase.mp hi
      exact Finset.mem_erase.mpr (And.intro hMem.1
        ((Finset.mem_powersetCard.mp hPower).1 hMem.2))
    have hCard : D.card = m := by
      dsimp only [D]
      rw [Finset.card_erase_of_mem hTa, (Finset.mem_powersetCard.mp hPower).2]
      omega
    have hD : Membership.mem B D := Finset.mem_powersetCard.mpr (And.intro hSub hCard)
    exact Exists.intro D (Exists.intro hD (Finset.insert_erase hTa))
  have hCount := Finset.card_bij g hTo hInj hOnto
  change C.card = _
  exact hCount.symm.trans (Finset.card_powersetCard m (S.erase a))

theorem hamiltonian_two_prescribed_subset_count
    (a b : I) (hab : Not (a = b)) (m : Nat) (hm : 1 <= m) :
    (((Finset.univ : Finset I).powersetCard m).filter
      (fun D => And (Membership.mem D a) (Not (Membership.mem D b)))).card =
        (Fintype.card I - 2).choose (m - 1) := by
  classical
  let S := (Finset.univ : Finset I).erase b
  have hSa : Membership.mem S a := Finset.mem_erase.mpr (And.intro hab (Finset.mem_univ _))
  have hSubIff (D : Finset I) : D <= S <-> Not (Membership.mem D b) := by
    apply Iff.intro
    case mp =>
      intro hSub hb
      have hx := hSub hb
      simp [S] at hx
    case mpr =>
      intro hb i hi
      exact Finset.mem_erase.mpr
        (And.intro (fun hib => hb (by rw [<- hib]; exact hi)) (Finset.mem_univ _))
  have hSets :
      ((Finset.univ : Finset I).powersetCard m).filter
        (fun D => And (Membership.mem D a) (Not (Membership.mem D b))) =
      (S.powersetCard m).filter (fun D => Membership.mem D a) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, hSubIff]
    exact Iff.intro
      (fun h => And.intro (And.intro h.2.2 h.1) h.2.1)
      (fun h => And.intro h.1.2 (And.intro h.2 h.1.1))
  have hCount := hamiltonian_prescribed_powerset_count S a hSa (m - 1)
  have hShift : m - 1 + 1 = m := by omega
  rw [hShift] at hCount
  have hSC : (S.erase a).card = Fintype.card I - 2 := by
    rw [Finset.card_erase_of_mem hSa]
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]
    omega
  rw [hSets, hCount, hSC]

def hamiltonianPrescribedBalancedSigns (m : Nat) (a b : I) : Finset (I -> Bool) :=
  Finset.univ.filter (fun e =>
    And ((hamiltonianSignCut e).card = m)
      (And (Membership.mem (hamiltonianSignCut e) a)
        (Not (Membership.mem (hamiltonianSignCut e) b))))

theorem hamiltonian_prescribed_balanced_sign_count
    (a b : I) (hab : Not (a = b)) (m : Nat) (hm : 1 <= m) :
    (hamiltonianPrescribedBalancedSigns m a b).card =
      (Fintype.card I - 2).choose (m - 1) := by
  classical
  have hSets :
      Finset.univ.filter (fun D : Finset I =>
        And (D.card = m) (And (Membership.mem D a) (Not (Membership.mem D b)))) =
      ((Finset.univ : Finset I).powersetCard m).filter
        (fun D => And (Membership.mem D a) (Not (Membership.mem D b))) := by
    ext D
    simp [Finset.mem_powersetCard]
  unfold hamiltonianPrescribedBalancedSigns
  rw [hamiltonian_sign_cut_filtered_count (fun D : Finset I =>
    And (D.card = m) (And (Membership.mem D a) (Not (Membership.mem D b)))), hSets]
  exact hamiltonian_two_prescribed_subset_count a b hab m hm

theorem hamiltonian_prescribed_balanced_sign_mass
    (a b : I) (hab : Not (a = b)) (m : Nat) (hm : 1 <= m)
    (hSize : Fintype.card I = 2 * m) :
    Fintype.card (I -> Bool) <= 4 * (Fintype.card I - 1) *
      (hamiltonianPrescribedBalancedSigns m a b).card := by
  rw [hamiltonian_sign_cube_card, hamiltonian_prescribed_balanced_sign_count a b hab m hm, hSize]
  have hCentral := hamiltonian_central_binomial_mass (m - 1)
  have hN : 2 * m - 2 = 2 * (m - 1) := by omega
  have hPred : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  have hPow : 2 ^ (2 * m) = 4 * 2 ^ (2 * (m - 1)) := by
    have hExp : 2 * m = 2 + 2 * (m - 1) := by omega
    rw [hExp, pow_add]
    norm_num
  rw [hN, hPred, hPow]
  exact (Nat.mul_le_mul_left 4 hCentral).trans_eq (by ring)

end PrimeFactorOscillations
