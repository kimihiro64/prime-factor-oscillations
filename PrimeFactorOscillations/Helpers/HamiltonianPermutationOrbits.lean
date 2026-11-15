/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.GroupTheory.Perm.Cycle.Basic
import PrimeFactorOscillations.Helpers.HamiltonianSubsetCancellation

/-! # Complete permutation orbits in the signed Hamiltonian coefficient

The finite orbit family includes singleton fixed-point orbits. Its union
has the actual ambient cardinality. The existing cycle-subset cancellation
therefore applies to an actual permutation, with no support omitted.
This is the orbit coefficient needed in the full determinant/permanent
consumer, whose regrouping is handled separately.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianPermutationOrbit (f : Equiv.Perm Iota) (x : Iota) : Finset Iota := by
  classical
  exact Finset.univ.filter (f.SameCycle x)

def hamiltonianPermutationOrbits (f : Equiv.Perm Iota) : Finset (Finset Iota) := by
  classical
  exact Finset.univ.image (hamiltonianPermutationOrbit f)

def hamiltonianOrbitUnion (C : Finset (Finset Iota)) : Finset Iota := by
  classical
  exact C.biUnion (fun A => A)

theorem mem_hamiltonianPermutationOrbit (f : Equiv.Perm Iota) (x y : Iota) :
    Membership.mem (hamiltonianPermutationOrbit f x) y <-> f.SameCycle x y := by
  classical
  simp only [hamiltonianPermutationOrbit, Finset.mem_filter, Finset.mem_univ, true_and]

theorem hamiltonianPermutationOrbit_nonempty (f : Equiv.Perm Iota) (x : Iota) :
    (hamiltonianPermutationOrbit f x).Nonempty :=
  Exists.intro x ((mem_hamiltonianPermutationOrbit f x x).mpr (Equiv.Perm.SameCycle.refl f x))

theorem hamiltonianPermutationOrbit_eq_iff (f : Equiv.Perm Iota) (x y : Iota) :
    hamiltonianPermutationOrbit f x = hamiltonianPermutationOrbit f y <-> f.SameCycle x y := by
  classical
  apply Iff.intro
  next =>
    intro h
    have hy := (mem_hamiltonianPermutationOrbit f y y).mpr (Equiv.Perm.SameCycle.refl f y)
    rw [<- h] at hy
    exact (mem_hamiltonianPermutationOrbit f x y).mp hy
  next =>
    intro h
    apply Finset.ext
    intro z
    rw [mem_hamiltonianPermutationOrbit, mem_hamiltonianPermutationOrbit]
    exact Iff.intro (fun hx => h.symm.trans hx) (fun hy => h.trans hy)

theorem hamiltonianPermutationOrbit_of_fixed (f : Equiv.Perm Iota) (x : Iota)
    (hFix : f x = x) :
    hamiltonianPermutationOrbit f x = {x} := by
  classical
  apply Finset.ext
  intro y
  rw [mem_hamiltonianPermutationOrbit, Finset.mem_singleton]
  apply Iff.intro
  next =>
    intro h
    exact (h.eq_of_left hFix).symm
  next =>
    intro h
    subst y
    exact Equiv.Perm.SameCycle.refl f x

theorem hamiltonianPermutationOrbit_mem (f : Equiv.Perm Iota) (x : Iota) :
    Membership.mem (hamiltonianPermutationOrbits f) (hamiltonianPermutationOrbit f x) := by
  classical
  exact Finset.mem_image_of_mem (hamiltonianPermutationOrbit f) (Finset.mem_univ x)

theorem hamiltonianPermutationOrbits_pairwise_disjoint (f : Equiv.Perm Iota) :
    (hamiltonianPermutationOrbits f : Set (Finset Iota)).Pairwise Disjoint := by
  classical
  intro A hA B hB hAB
  dsimp only [hamiltonianPermutationOrbits] at hA hB
  let left := Finset.mem_image.mp hA
  let right := Finset.mem_image.mp hB
  let x := left.choose
  let y := right.choose
  have hx : hamiltonianPermutationOrbit f x = A := left.choose_spec.2
  have hy : hamiltonianPermutationOrbit f y = B := right.choose_spec.2
  apply Finset.disjoint_left.mpr
  intro z hzA hzB
  rw [<- hx, mem_hamiltonianPermutationOrbit] at hzA
  rw [<- hy, mem_hamiltonianPermutationOrbit] at hzB
  have hxy := hzA.trans hzB.symm
  have hOrbit := (hamiltonianPermutationOrbit_eq_iff f x y).mpr hxy
  exact hAB (hx.symm.trans (hOrbit.trans hy))

theorem hamiltonianOrbitUnion_all (f : Equiv.Perm Iota) :
    hamiltonianOrbitUnion (hamiltonianPermutationOrbits f) = Finset.univ := by
  classical
  apply Finset.ext
  intro x
  apply Iff.intro
  next =>
    intro h
    exact Finset.mem_univ x
  next =>
    intro h
    change Membership.mem ((hamiltonianPermutationOrbits f).biUnion (fun A => A)) x
    apply Finset.mem_biUnion.mpr
    exact Exists.intro (hamiltonianPermutationOrbit f x)
      (And.intro (hamiltonianPermutationOrbit_mem f x)
        ((mem_hamiltonianPermutationOrbit f x x).mpr (Equiv.Perm.SameCycle.refl f x)))

theorem hamiltonianOrbitUnion_card (f : Equiv.Perm Iota) (C : Finset (Finset Iota))
    (hC : C <= hamiltonianPermutationOrbits f) :
    (hamiltonianOrbitUnion C).card = Finset.sum C (fun A => A.card) := by
  classical
  apply Finset.card_biUnion
  intro A hA B hB hAB
  exact hamiltonianPermutationOrbits_pairwise_disjoint f (hC hA) (hC hB) hAB

theorem hamiltonianPermutationOrbit_card_sum (f : Equiv.Perm Iota) :
    Finset.sum (hamiltonianPermutationOrbits f) (fun A => A.card) = Fintype.card Iota := by
  classical
  rw [<- hamiltonianOrbitUnion_card f (hamiltonianPermutationOrbits f) (le_refl _),
    hamiltonianOrbitUnion_all, Finset.card_univ]

def hamiltonianPermutationOrbitCoefficient [CommRing R] (f : Equiv.Perm Iota) : R :=
  -Finset.sum (hamiltonianPermutationOrbits f).powerset
    (fun C => (-1 : R) ^ C.card * ((hamiltonianOrbitUnion C).card : R))

theorem hamiltonianPermutationOrbitCoefficient_eq [CommRing R] (f : Equiv.Perm Iota) :
    hamiltonianPermutationOrbitCoefficient (R := R) f =
      if (hamiltonianPermutationOrbits f).card = 1 then (Fintype.card Iota : R) else 0 := by
  classical
  have hSum :
      Finset.sum (hamiltonianPermutationOrbits f).powerset
          (fun C => (-1 : R) ^ C.card * ((hamiltonianOrbitUnion C).card : R)) =
        Finset.sum (hamiltonianPermutationOrbits f).powerset
          (fun C => (-1 : R) ^ C.card * Finset.sum C (fun A => (A.card : R))) := by
    apply Finset.sum_congr rfl
    intro C hC
    rw [hamiltonianOrbitUnion_card f C (Finset.mem_powerset.mp hC), Nat.cast_sum]
  have hTotal : Finset.sum (hamiltonianPermutationOrbits f) (fun A => (A.card : R)) =
      (Fintype.card Iota : R) := by
    have h := congrArg (fun m : Nat => (m : R)) (hamiltonianPermutationOrbit_card_sum f)
    simpa only [Nat.cast_sum] using h
  have hIso := cycleSubsetIsolation (R := R) (hamiltonianPermutationOrbits f)
    (fun A => (A.card : R))
  rw [hTotal] at hIso
  unfold hamiltonianPermutationOrbitCoefficient
  rw [hSum]
  exact hIso


def hamiltonianPermutationInvariant (f : Equiv.Perm Iota) (S : Finset Iota) : Prop :=
  forall x, Membership.mem S (f x) <-> Membership.mem S x

def hamiltonianSelectedOrbits (f : Equiv.Perm Iota) (S : Finset Iota) :
    Finset (Finset Iota) := by
  classical
  exact (hamiltonianPermutationOrbits f).filter (fun A => A <= S)

theorem hamiltonianPermutationOrbit_invariant (f : Equiv.Perm Iota) (x : Iota) :
    hamiltonianPermutationInvariant f (hamiltonianPermutationOrbit f x) := by
  classical
  intro y
  rw [mem_hamiltonianPermutationOrbit, mem_hamiltonianPermutationOrbit]
  exact Equiv.Perm.sameCycle_apply_right

theorem hamiltonianInvariant_sameCycle (f : Equiv.Perm Iota) (S : Finset Iota)
    (hS : hamiltonianPermutationInvariant f S) (x y : Iota) (hxy : f.SameCycle x y) :
    Membership.mem S x <-> Membership.mem S y := by
  have hPow : forall k : Nat, forall z : Iota,
      Membership.mem S ((f ^ k) z) <-> Membership.mem S z := by
    intro k
    induction k with
    | zero =>
      intro z
      simp only [pow_zero, Equiv.Perm.one_apply]
    | succ k ih =>
      intro z
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact (ih (f z)).trans (hS z)
  let witness := hxy.exists_nat_pow_eq
  have h := hPow witness.choose x
  rw [witness.choose_spec] at h
  exact h.symm

theorem hamiltonianPermutationOrbit_subset_of_invariant (f : Equiv.Perm Iota)
    (S : Finset Iota) (hS : hamiltonianPermutationInvariant f S)
    (x : Iota) (hx : Membership.mem S x) :
    hamiltonianPermutationOrbit f x <= S := by
  intro y hy
  exact (hamiltonianInvariant_sameCycle f S hS x y
    ((mem_hamiltonianPermutationOrbit f x y).mp hy)).mp hx

theorem hamiltonianOrbitUnion_invariant (f : Equiv.Perm Iota) (C : Finset (Finset Iota))
    (hC : C <= hamiltonianPermutationOrbits f) :
    hamiltonianPermutationInvariant f (hamiltonianOrbitUnion C) := by
  classical
  have hAInv : forall A, Membership.mem C A -> hamiltonianPermutationInvariant f A := by
    intro A hA
    have hAll := hC hA
    dsimp only [hamiltonianPermutationOrbits] at hAll
    let rep := Finset.mem_image.mp hAll
    have hRep : hamiltonianPermutationOrbit f rep.choose = A := rep.choose_spec.2
    rw [<- hRep]
    exact hamiltonianPermutationOrbit_invariant f rep.choose
  intro x
  dsimp only [hamiltonianOrbitUnion]
  simp only [Finset.mem_biUnion]
  apply Iff.intro
  next =>
    intro h
    exact Exists.intro h.choose
      (And.intro h.choose_spec.1
        ((hAInv h.choose h.choose_spec.1 x).mp h.choose_spec.2))
  next =>
    intro h
    exact Exists.intro h.choose
      (And.intro h.choose_spec.1
        ((hAInv h.choose h.choose_spec.1 x).mpr h.choose_spec.2))

theorem hamiltonianOrbitUnion_selected (f : Equiv.Perm Iota) (S : Finset Iota)
    (hS : hamiltonianPermutationInvariant f S) :
    hamiltonianOrbitUnion (hamiltonianSelectedOrbits f S) = S := by
  classical
  apply Finset.ext
  intro x
  apply Iff.intro
  next =>
    intro hx
    have h := Finset.mem_biUnion.mp hx
    have hSelected := Finset.mem_filter.mp h.choose_spec.1
    exact hSelected.2 h.choose_spec.2
  next =>
    intro hx
    apply Finset.mem_biUnion.mpr
    refine Exists.intro (hamiltonianPermutationOrbit f x) (And.intro ?_ ?_)
    next =>
      apply Finset.mem_filter.mpr
      exact And.intro (hamiltonianPermutationOrbit_mem f x)
        (hamiltonianPermutationOrbit_subset_of_invariant f S hS x hx)
    next =>
      exact (mem_hamiltonianPermutationOrbit f x x).mpr (Equiv.Perm.SameCycle.refl f x)

theorem hamiltonianPermutationOrbits_member_nonempty (f : Equiv.Perm Iota)
    (A : Finset Iota) (hA : Membership.mem (hamiltonianPermutationOrbits f) A) :
    A.Nonempty := by
  classical
  dsimp only [hamiltonianPermutationOrbits] at hA
  let rep := Finset.mem_image.mp hA
  have hRep : hamiltonianPermutationOrbit f rep.choose = A := rep.choose_spec.2
  rw [<- hRep]
  exact hamiltonianPermutationOrbit_nonempty f rep.choose

theorem hamiltonianOrbit_subset_union_iff (f : Equiv.Perm Iota)
    (C : Finset (Finset Iota)) (hC : C <= hamiltonianPermutationOrbits f)
    (A : Finset Iota) (hA : Membership.mem (hamiltonianPermutationOrbits f) A) :
    A <= hamiltonianOrbitUnion C <-> Membership.mem C A := by
  classical
  apply Iff.intro
  next =>
    intro hSub
    let witness := hamiltonianPermutationOrbits_member_nonempty f A hA
    let x := witness.choose
    have hx : Membership.mem A x := witness.choose_spec
    have hUnion := hSub hx
    have h := Finset.mem_biUnion.mp hUnion
    let B := h.choose
    have hB : Membership.mem C B := h.choose_spec.1
    have hxB : Membership.mem B x := h.choose_spec.2
    have hEq : A = B := Classical.byContradiction (fun hne =>
      (Finset.disjoint_left.mp
        (hamiltonianPermutationOrbits_pairwise_disjoint f hA (hC hB) hne)) hx hxB)
    rw [hEq]
    exact hB
  next =>
    intro hAC x hx
    apply Finset.mem_biUnion.mpr
    exact Exists.intro A (And.intro hAC hx)

theorem hamiltonianSelectedOrbits_union (f : Equiv.Perm Iota)
    (C : Finset (Finset Iota)) (hC : C <= hamiltonianPermutationOrbits f) :
    hamiltonianSelectedOrbits f (hamiltonianOrbitUnion C) = C := by
  classical
  apply Finset.ext
  intro A
  apply Iff.intro
  next =>
    intro h
    have hFilter := Finset.mem_filter.mp h
    exact (hamiltonianOrbit_subset_union_iff f C hC A hFilter.1).mp hFilter.2
  next =>
    intro h
    apply Finset.mem_filter.mpr
    exact And.intro (hC h) ((hamiltonianOrbit_subset_union_iff f C hC A (hC h)).mpr h)

def hamiltonianOrbitInvariantEquiv (f : Equiv.Perm Iota) :
    Equiv {C : Finset (Finset Iota) // C <= hamiltonianPermutationOrbits f}
      {S : Finset Iota // hamiltonianPermutationInvariant f S} := by
  classical
  exact {
    toFun := fun C => Subtype.mk (hamiltonianOrbitUnion C.val)
      (hamiltonianOrbitUnion_invariant f C.val C.property)
    invFun := fun S => Subtype.mk (hamiltonianSelectedOrbits f S.val)
      (by intro A hA; exact (Finset.mem_filter.mp hA).1)
    left_inv := by
      intro C
      apply Subtype.ext
      exact hamiltonianSelectedOrbits_union f C.val C.property
    right_inv := by
      intro S
      apply Subtype.ext
      exact hamiltonianOrbitUnion_selected f S.val S.property }

end PrimeFactorOscillations
