/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeEntropy

/-! # Actual directed cycle counts and reversal classes -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianDirectedCycles (R : Iota -> Iota -> Prop) : Finset (Equiv.Perm Iota) := by
  classical
  exact Finset.univ.filter (fun f =>
    (hamiltonianPermutationOrbits f).card = 1 /\ forall i, R (f i) i)

def hamiltonianUnorientedCycles (R : Iota -> Iota -> Prop) :
    Finset (Finset (Equiv.Perm Iota)) := by
  classical
  exact (hamiltonianDirectedCycles R).image (fun f => {f, f.symm})

theorem hamiltonian_indicator_cycle_count (R : Iota -> Iota -> Prop) [DecidableRel R] :
    hamiltonianCycleSum (fun i j => if R i j then (1 : Real) else 0) =
      ((hamiltonianDirectedCycles R).card : Real) := by
  classical
  have hProduct (f : Equiv.Perm Iota) :
      Finset.univ.prod (fun i => if R (f i) i then (1 : Real) else 0) =
        if forall i, R (f i) i then 1 else 0 := by
    by_cases h : forall i, R (f i) i
    . simp [h]
    . rw [if_neg h]
      have hw : exists i, Not (R (f i) i) := Classical.not_forall.mp h
      choose i hi using hw
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi, ite_false])
  unfold hamiltonianCycleSum
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [hamiltonianDirectedCycles, Finset.sum_filter, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro f hf
  rw [hProduct]
  by_cases hC : (hamiltonianPermutationOrbits f).card = 1
  . simp only [hC, true_and, ite_true]
  . simp only [hC, false_and, ite_false]

theorem hamiltonian_permutation_orbit_inverse (f : Equiv.Perm Iota) (x : Iota) :
    hamiltonianPermutationOrbit f.symm x = hamiltonianPermutationOrbit f x := by
  apply Finset.ext
  intro y
  rw [mem_hamiltonianPermutationOrbit, mem_hamiltonianPermutationOrbit]
  exact Equiv.Perm.sameCycle_inv

theorem hamiltonian_permutation_orbits_inverse (f : Equiv.Perm Iota) :
    hamiltonianPermutationOrbits f.symm = hamiltonianPermutationOrbits f := by
  unfold hamiltonianPermutationOrbits
  apply congrArg (fun g : Iota -> Finset Iota => Finset.univ.image g)
  funext x
  exact hamiltonian_permutation_orbit_inverse f x

theorem hamiltonian_directed_cycle_inverse (R : Iota -> Iota -> Prop)
    (hSymm : forall i j, R i j -> R j i) (f : Equiv.Perm Iota)
    (hf : Membership.mem (hamiltonianDirectedCycles R) f) :
    Membership.mem (hamiltonianDirectedCycles R) f.symm := by
  classical
  have h := (Finset.mem_filter.mp hf).2
  apply Finset.mem_filter.mpr
  refine And.intro (Finset.mem_univ _) (And.intro ?_ ?_)
  . rw [hamiltonian_permutation_orbits_inverse]
    exact h.1
  . intro i
    have he := h.2 (f.symm i)
    rw [f.apply_symm_apply] at he
    exact hSymm _ _ he

theorem hamiltonian_single_orbit_same_cycle (f : Equiv.Perm Iota)
    (hOne : (hamiltonianPermutationOrbits f).card = 1) (x y : Iota) :
    f.SameCycle x y := by
  classical
  choose A hA using Finset.card_eq_one.mp hOne
  have hx := hamiltonianPermutationOrbit_mem f x
  have hy := hamiltonianPermutationOrbit_mem f y
  rw [hA, Finset.mem_singleton] at hx hy
  exact (hamiltonianPermutationOrbit_eq_iff f x y).mp (hx.trans hy.symm)

theorem hamiltonian_single_orbit_not_inverse (f : Equiv.Perm Iota)
    (hCard : 3 <= Fintype.card Iota)
    (hOne : (hamiltonianPermutationOrbits f).card = 1) : Not (f.symm = f) := by
  classical
  intro hInv
  have hNonempty : Nonempty Iota := Fintype.card_pos_iff.mp (by omega)
  let x := Classical.choice hNonempty
  have hTwice (y : Iota) : f (f y) = y := by
    calc
      _ = f.symm (f y) := congrArg (fun p : Equiv.Perm Iota => p (f y)) hInv.symm
      _ = y := f.symm_apply_apply y
  have hPowers : forall k : Nat, Or ((f ^ k) x = x) ((f ^ k) x = f x) := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        cases ih with
        | inl h => rw [h]; exact Or.inr rfl
        | inr h => rw [h, hTwice]; exact Or.inl rfl
  have hAll : forall y : Iota, Membership.mem ({x, f x} : Finset Iota) y := by
    intro y
    choose k hk using (hamiltonian_single_orbit_same_cycle f hOne x y).exists_nat_pow_eq
    have h := hPowers k
    rw [hk] at h
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact h
  have hSub : forall y, Membership.mem (Finset.univ : Finset Iota) y ->
      Membership.mem ({x, f x} : Finset Iota) y := fun y _ => hAll y
  have hBound := Finset.card_le_card hSub
  have hPair : ({x, f x} : Finset Iota).card <= 2 := by
    simpa only [Finset.card_singleton] using Finset.card_insert_le x ({f x} : Finset Iota)
  rw [Finset.card_univ] at hBound
  omega

variable {Alpha : Type*} [DecidableEq Alpha]

theorem hamiltonian_free_involution_card
    (S : Finset Alpha) (f : Alpha -> Alpha)
    (hInvol : Function.Involutive f)
    (hClosed : forall x, Membership.mem S x -> Membership.mem S (f x))
    (hFree : forall x, Membership.mem S x -> Not (f x = x)) :
    S.card = 2 * (S.image (fun x => ({x, f x} : Finset Alpha))).card := by
  classical
  let C := S.image (fun x => ({x, f x} : Finset Alpha))
  have hPairEq (x z : Alpha) (hz : Membership.mem ({x, f x} : Finset Alpha) z) :
      ({z, f z} : Finset Alpha) = {x, f x} := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    cases hz with
    | inl h => rw [h]
    | inr h => rw [h, hInvol]; exact Finset.pair_comm _ _
  have hDisjoint : (C : Set (Finset Alpha)).Pairwise Disjoint := by
    intro A hA B hB hNe
    choose x hx hxA using Finset.mem_image.mp hA
    choose y hy hyB using Finset.mem_image.mp hB
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    rw [<- hxA] at hzA
    rw [<- hyB] at hzB
    have hEq := (hPairEq x z hzA).symm.trans (hPairEq y z hzB)
    exact hNe (hxA.symm.trans (hEq.trans hyB))
  have hUnion : C.biUnion (fun A => A) = S := by
    apply Finset.ext
    intro z
    constructor
    . intro hz
      choose A hA hzA using Finset.mem_biUnion.mp hz
      choose x hx hxA using Finset.mem_image.mp hA
      rw [<- hxA] at hzA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzA
      cases hzA with
      | inl h => rw [h]; exact hx
      | inr h => rw [h]; exact hClosed x hx
    . intro hz
      apply Finset.mem_biUnion.mpr
      exact Exists.intro {z, f z} (And.intro
        (Finset.mem_image_of_mem _ hz) (Finset.mem_insert_self _ _))
  have hTwo : forall A, Membership.mem C A -> A.card = 2 := by
    intro A hA
    choose x hx hxA using Finset.mem_image.mp hA
    rw [<- hxA]
    exact Finset.card_pair_eq_two_iff.mpr (Ne.symm (hFree x hx))
  calc
    S.card = (C.biUnion (fun A => A)).card := congrArg Finset.card hUnion.symm
    _ = Finset.sum C (fun A => A.card) := Finset.card_biUnion hDisjoint
    _ = Finset.sum C (fun _ => 2) := Finset.sum_congr rfl (fun A hA => hTwo A hA)
    _ = 2 * C.card := by simp only [Finset.sum_const, smul_eq_mul]; omega

theorem hamiltonian_unoriented_cycle_card (R : Iota -> Iota -> Prop)
    (hSymm : forall i j, R i j -> R j i) (hCard : 3 <= Fintype.card Iota) :
    (hamiltonianDirectedCycles R).card = 2 * (hamiltonianUnorientedCycles R).card := by
  classical
  apply hamiltonian_free_involution_card (hamiltonianDirectedCycles R)
    (fun f : Equiv.Perm Iota => f.symm)
  . intro f
    exact f.symm_symm
  . exact hamiltonian_directed_cycle_inverse R hSymm
  . intro f hf
    exact hamiltonian_single_orbit_not_inverse f hCard (Finset.mem_filter.mp hf).2.1

end PrimeFactorOscillations
