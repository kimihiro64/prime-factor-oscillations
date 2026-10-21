/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassRankCoordinates

/-! # Exact products over the actual finite prime class -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

theorem primeClassRankValue_surjective_below (P : Set Nat) (X p : Nat)
    (hp : Membership.mem (primeClassPrefix P X) p) :
    exists r : Nat, And (r < (primeClassPrefix P X).card)
      (primeClassRankValue P r = p) := by
  classical
  have hm : And (And (2 <= p) (p <= X)) (And (Nat.Prime p) (Membership.mem P p)) := by
    simpa only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc] using hp
  let r := (primeClassPrefix P (p - 1)).card
  have hr : r < (primeClassPrefix P X).card := by
    have h := primeClassPrefix_rank_lt P p (X + 1) hm.2.1 hm.2.2 (by omega)
    simpa only [Nat.add_sub_cancel] using h
  exact Exists.intro r (And.intro hr
    (primeClassRankValue_eq_of_rank P p r hm.2.1 hm.2.2 rfl))

theorem primeClassCoordinates_map {A B : Type*} (P : Set Nat) (f : Nat -> A)
    (g : A -> B) (X : Nat) :
    (primeClassCoordinates P f X).map g = primeClassCoordinates P (fun p => g (f p)) X := by
  simp only [primeClassCoordinates, List.map_ofFn, Function.comp_def]

theorem primeClassCoordinates_prod {M : Type*} [CommMonoid M]
    (P : Set Nat) (f : Nat -> M) (X : Nat) :
    (primeClassCoordinates P f X).prod = (primeClassPrefix P X).prod f := by
  classical
  rw [primeClassCoordinates, List.prod_ofFn]
  apply Finset.prod_bij (fun i _ => primeClassRankValue P i.val)
  next =>
    intro i hi
    have h := primeClassRankValue_spec P X i.val i.isLt
    simpa only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc] using
      And.intro (And.intro h.1.two_le h.2.2.1) (And.intro h.1 h.2.1)
  next =>
    intro i hi j hj hij
    apply Fin.ext
    exact primeClassRankValue_injective_below P X i.val j.val i.isLt j.isLt hij
  next =>
    intro p hp
    choose r hr using primeClassRankValue_surjective_below P X p hp
    exact Exists.intro (Fin.mk r hr.1) (Exists.intro (Finset.mem_univ _) hr.2)
  next =>
    intro i hi
    rfl

theorem primeClassCoordinates_nonneg (P : Set Nat) (f : Nat -> Real) (X : Nat)
    (hf : forall p : Nat, Nat.Prime p -> 0 <= f p) :
    forall a : Real, List.Mem a (primeClassCoordinates P f X) -> 0 <= a := by
  intro a ha
  choose r hr using (primeClassCoordinates_mem_iff P f X a).mp ha
  have h := hf (primeClassRankValue P r) (primeClassRankValue_spec P X r hr.1).1
  simpa only [hr.2] using h

end PrimeFactorOscillations.PrimeClassDeletion
