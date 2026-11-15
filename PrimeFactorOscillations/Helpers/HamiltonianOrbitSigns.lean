/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.GroupTheory.Perm.Cycle.Factors
import PrimeFactorOscillations.Helpers.HamiltonianPermutationOrbits

/-! # Actual restricted-permutation signs in the Hamiltonian coefficient

An invariant-set mask applies the original permutation on that set and
fixes the complement. Its sign is exactly the sign of the restricted
permutation. Disjoint invariant masks multiply with every term retained.
A singleton fixed-point orbit supplies the same negative orbit factor as
each nontrivial cycle after multiplication by the full cardinal parity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianPermutationMask (f : Equiv.Perm Iota) (S : Finset Iota)
    (hS : hamiltonianPermutationInvariant f S) : Equiv.Perm Iota := by
  classical
  exact Equiv.Perm.ofSubtype
    (Equiv.Perm.subtypePerm f (p := fun x => Membership.mem S x) hS)

theorem hamiltonianPermutationMask_congr (f : Equiv.Perm Iota)
    (S T : Finset Iota) (hS : hamiltonianPermutationInvariant f S)
    (hT : hamiltonianPermutationInvariant f T) (hST : S = T) :
    hamiltonianPermutationMask f S hS = hamiltonianPermutationMask f T hT := by
  subst T
  rfl

theorem hamiltonianPermutationMask_apply_of_mem (f : Equiv.Perm Iota)
    (S : Finset Iota) (hS : hamiltonianPermutationInvariant f S)
    (x : Iota) (hx : Membership.mem S x) :
    hamiltonianPermutationMask f S hS x = f x := by
  classical
  exact Equiv.Perm.ofSubtype_apply_of_mem
    (Equiv.Perm.subtypePerm f (p := fun y => Membership.mem S y) hS) hx

theorem hamiltonianPermutationMask_apply_of_not_mem (f : Equiv.Perm Iota)
    (S : Finset Iota) (hS : hamiltonianPermutationInvariant f S)
    (x : Iota) (hx : Not (Membership.mem S x)) :
    hamiltonianPermutationMask f S hS x = x := by
  classical
  exact Equiv.Perm.ofSubtype_apply_of_not_mem
    (Equiv.Perm.subtypePerm f (p := fun y => Membership.mem S y) hS) hx

theorem hamiltonianPermutationMask_sign (f : Equiv.Perm Iota)
    (S : Finset Iota) (hS : hamiltonianPermutationInvariant f S) :
    Equiv.Perm.sign (hamiltonianPermutationMask f S hS) =
      Equiv.Perm.sign (Equiv.Perm.subtypePerm f (p := fun x => Membership.mem S x) hS) := by
  classical
  exact Equiv.Perm.sign_ofSubtype _

theorem hamiltonianPermutationMask_empty (f : Equiv.Perm Iota)
    (hEmpty : hamiltonianPermutationInvariant f EmptyCollection.emptyCollection) :
    hamiltonianPermutationMask f EmptyCollection.emptyCollection hEmpty = 1 := by
  classical
  apply Equiv.ext
  intro x
  exact hamiltonianPermutationMask_apply_of_not_mem f EmptyCollection.emptyCollection hEmpty x
    (Finset.notMem_empty x)

theorem hamiltonianPermutationMask_union (f : Equiv.Perm Iota)
    (S T : Finset Iota) (hS : hamiltonianPermutationInvariant f S)
    (hT : hamiltonianPermutationInvariant f T)
    (hU : hamiltonianPermutationInvariant f (Union.union S T)) (hDisjoint : Disjoint S T) :
    hamiltonianPermutationMask f (Union.union S T) hU =
      hamiltonianPermutationMask f S hS * hamiltonianPermutationMask f T hT := by
  classical
  apply Equiv.ext
  intro x
  by_cases hxT : Membership.mem T x
  next =>
    have hfT : Membership.mem T (f x) := (hT x).mpr hxT
    have hfS : Not (Membership.mem S (f x)) := by
      intro h
      exact (Finset.disjoint_left.mp hDisjoint) h hfT
    have hxU : Membership.mem (Union.union S T) x := Finset.mem_union.mpr (Or.inr hxT)
    rw [hamiltonianPermutationMask_apply_of_mem f (Union.union S T) hU x hxU,
      Equiv.Perm.mul_apply, hamiltonianPermutationMask_apply_of_mem f T hT x hxT,
      hamiltonianPermutationMask_apply_of_not_mem f S hS (f x) hfS]
  next =>
    by_cases hxS : Membership.mem S x
    next =>
      have hxU : Membership.mem (Union.union S T) x := Finset.mem_union.mpr (Or.inl hxS)
      rw [hamiltonianPermutationMask_apply_of_mem f (Union.union S T) hU x hxU,
        Equiv.Perm.mul_apply, hamiltonianPermutationMask_apply_of_not_mem f T hT x hxT,
        hamiltonianPermutationMask_apply_of_mem f S hS x hxS]
    next =>
      have hxU : Not (Membership.mem (Union.union S T) x) := by
        intro h
        exact (Finset.mem_union.mp h).elim hxS hxT
      rw [hamiltonianPermutationMask_apply_of_not_mem f (Union.union S T) hU x hxU,
        Equiv.Perm.mul_apply, hamiltonianPermutationMask_apply_of_not_mem f T hT x hxT,
        hamiltonianPermutationMask_apply_of_not_mem f S hS x hxS]

theorem hamiltonianPermutationMask_orbit (f : Equiv.Perm Iota) (x : Iota) :
    hamiltonianPermutationMask f (hamiltonianPermutationOrbit f x)
        (hamiltonianPermutationOrbit_invariant f x) = f.cycleOf x := by
  classical
  apply Equiv.ext
  intro y
  by_cases hy : f.SameCycle x y
  next =>
    rw [Equiv.Perm.cycleOf_apply, if_pos hy,
      hamiltonianPermutationMask_apply_of_mem f (hamiltonianPermutationOrbit f x)
        (hamiltonianPermutationOrbit_invariant f x) y
        ((mem_hamiltonianPermutationOrbit f x y).mpr hy)]
  next =>
    have hNot : Not (Membership.mem (hamiltonianPermutationOrbit f x) y) := by
      intro h
      exact hy ((mem_hamiltonianPermutationOrbit f x y).mp h)
    rw [Equiv.Perm.cycleOf_apply, if_neg hy,
      hamiltonianPermutationMask_apply_of_not_mem f (hamiltonianPermutationOrbit f x)
        (hamiltonianPermutationOrbit_invariant f x) y hNot]

theorem hamiltonianPermutationMask_orbit_sign (f : Equiv.Perm Iota) (x : Iota) :
    (-1 : Units Int) ^ (hamiltonianPermutationOrbit f x).card *
      Equiv.Perm.sign (hamiltonianPermutationMask f (hamiltonianPermutationOrbit f x)
        (hamiltonianPermutationOrbit_invariant f x)) = -1 := by
  classical
  rw [hamiltonianPermutationMask_orbit]
  by_cases hFix : f x = x
  next =>
    have hOne : f.cycleOf x = 1 := (Equiv.Perm.cycleOf_eq_one_iff f).mpr hFix
    rw [hOne, hamiltonianPermutationOrbit_of_fixed f x hFix]
    simp
  next =>
    have hCycle := Equiv.Perm.isCycle_cycleOf f hFix
    have hSupport : (f.cycleOf x).support = hamiltonianPermutationOrbit f x := by
      apply Finset.ext
      intro y
      rw [Equiv.Perm.mem_support_cycleOf_iff' hFix, mem_hamiltonianPermutationOrbit]
    rw [hCycle.sign, hSupport]
    have hSquare : (-1 : Units Int) ^ (hamiltonianPermutationOrbit f x).card *
        (-1 : Units Int) ^ (hamiltonianPermutationOrbit f x).card = 1 := by
      rw [<- mul_pow]
      simp
    rw [mul_neg, hSquare]


theorem hamiltonianPermutationMask_member_sign (f : Equiv.Perm Iota)
    (A : Finset Iota) (hA : Membership.mem (hamiltonianPermutationOrbits f) A)
    (hInv : hamiltonianPermutationInvariant f A) :
    (-1 : Units Int) ^ A.card *
      Equiv.Perm.sign (hamiltonianPermutationMask f A hInv) = -1 := by
  classical
  dsimp only [hamiltonianPermutationOrbits] at hA
  let rep := Finset.mem_image.mp hA
  have hRep : hamiltonianPermutationOrbit f rep.choose = A := rep.choose_spec.2
  have h := hamiltonianPermutationMask_orbit_sign f rep.choose
  have hMask := hamiltonianPermutationMask_congr f
    (hamiltonianPermutationOrbit f rep.choose) A
    (hamiltonianPermutationOrbit_invariant f rep.choose) hInv hRep
  rw [congrArg Finset.card hRep, hMask] at h
  exact h

theorem hamiltonianPermutationMask_selected_sign (f : Equiv.Perm Iota)
    (C : Finset (Finset Iota)) (hC : C <= hamiltonianPermutationOrbits f) :
    (-1 : Units Int) ^ (hamiltonianOrbitUnion C).card *
      Equiv.Perm.sign (hamiltonianPermutationMask f (hamiltonianOrbitUnion C)
        (hamiltonianOrbitUnion_invariant f C hC)) = (-1) ^ C.card := by
  classical
  revert hC
  induction C using Finset.induction_on with
  | empty =>
    intro hC
    have hMask : hamiltonianPermutationMask f (hamiltonianOrbitUnion EmptyCollection.emptyCollection)
        (hamiltonianOrbitUnion_invariant f EmptyCollection.emptyCollection hC) = 1 := by
      apply Equiv.ext
      intro x
      apply hamiltonianPermutationMask_apply_of_not_mem
      simp [hamiltonianOrbitUnion]
    rw [hMask]
    simp [hamiltonianOrbitUnion]
  | @insert A C hNot ih =>
    intro hC
    have hA : Membership.mem (hamiltonianPermutationOrbits f) A :=
      hC (Finset.mem_insert.mpr (Or.inl rfl))
    have hSub : C <= hamiltonianPermutationOrbits f := by
      intro B hB
      exact hC (Finset.mem_insert.mpr (Or.inr hB))
    have hAInv : hamiltonianPermutationInvariant f A := by
      dsimp only [hamiltonianPermutationOrbits] at hA
      let rep := Finset.mem_image.mp hA
      have hRep : hamiltonianPermutationOrbit f rep.choose = A := rep.choose_spec.2
      rw [<- hRep]
      exact hamiltonianPermutationOrbit_invariant f rep.choose
    have hU := hamiltonianOrbitUnion_invariant f C hSub
    have hDisjoint : Disjoint A (hamiltonianOrbitUnion C) := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxU
      let witness := Finset.mem_biUnion.mp hxU
      have hB : Membership.mem C witness.choose := witness.choose_spec.1
      have hNe : Not (A = witness.choose) := by
        intro h
        exact hNot (by rw [h]; exact hB)
      exact (Finset.disjoint_left.mp
        (hamiltonianPermutationOrbits_pairwise_disjoint f hA (hSub hB) hNe))
          hxA witness.choose_spec.2
    have hUnion : hamiltonianOrbitUnion (insert A C) =
        Union.union A (hamiltonianOrbitUnion C) := by
      simp only [hamiltonianOrbitUnion, Finset.biUnion_insert]
    have hCard : (hamiltonianOrbitUnion (insert A C)).card =
        A.card + (hamiltonianOrbitUnion C).card := by
      rw [hamiltonianOrbitUnion_card f (insert A C) hC, Finset.sum_insert hNot,
        <- hamiltonianOrbitUnion_card f C hSub]
    have hMask : hamiltonianPermutationMask f (hamiltonianOrbitUnion (insert A C))
        (hamiltonianOrbitUnion_invariant f (insert A C) hC) =
        hamiltonianPermutationMask f A hAInv *
          hamiltonianPermutationMask f (hamiltonianOrbitUnion C) hU := by
      have hUU : hamiltonianPermutationInvariant f
          (Union.union A (hamiltonianOrbitUnion C)) := by
        intro x
        simp only [Finset.mem_union]
        exact or_congr (hAInv x) (hU x)
      exact (hamiltonianPermutationMask_congr f _ _
        (hamiltonianOrbitUnion_invariant f (insert A C) hC) hUU hUnion).trans
          (hamiltonianPermutationMask_union f A (hamiltonianOrbitUnion C)
            hAInv hU hUU hDisjoint)
    rw [hCard, hMask, map_mul, pow_add, Finset.card_insert_of_notMem hNot, pow_succ]
    calc
      (-1 : Units Int) ^ A.card * (-1) ^ (hamiltonianOrbitUnion C).card *
          (Equiv.Perm.sign (hamiltonianPermutationMask f A hAInv) *
            Equiv.Perm.sign (hamiltonianPermutationMask f (hamiltonianOrbitUnion C) hU)) =
          ((-1 : Units Int) ^ A.card *
            Equiv.Perm.sign (hamiltonianPermutationMask f A hAInv)) *
          ((-1 : Units Int) ^ (hamiltonianOrbitUnion C).card *
            Equiv.Perm.sign (hamiltonianPermutationMask f (hamiltonianOrbitUnion C) hU)) := by
        ac_rfl
      _ = (-1 : Units Int) * (-1) ^ C.card := by
        rw [hamiltonianPermutationMask_member_sign f A hA hAInv, ih hSub]
      _ = (-1 : Units Int) ^ C.card * (-1) := mul_comm _ _

theorem hamiltonianInvariant_restriction_sign (f : Equiv.Perm Iota)
    (S : Finset Iota) (hS : hamiltonianPermutationInvariant f S) :
    (-1 : Units Int) ^ S.card *
      Equiv.Perm.sign (Equiv.Perm.subtypePerm f (p := fun x => Membership.mem S x) hS) =
        (-1) ^ (hamiltonianSelectedOrbits f S).card := by
  classical
  have hSelected : hamiltonianSelectedOrbits f S <= hamiltonianPermutationOrbits f := by
    intro A hA
    exact (Finset.mem_filter.mp hA).1
  have h := hamiltonianPermutationMask_selected_sign f
    (hamiltonianSelectedOrbits f S) hSelected
  have hUnion := hamiltonianOrbitUnion_selected f S hS
  have hMask := hamiltonianPermutationMask_congr f _ S
    (hamiltonianOrbitUnion_invariant f (hamiltonianSelectedOrbits f S) hSelected) hS hUnion
  rw [congrArg Finset.card hUnion, hMask, hamiltonianPermutationMask_sign] at h
  exact h

end PrimeFactorOscillations
