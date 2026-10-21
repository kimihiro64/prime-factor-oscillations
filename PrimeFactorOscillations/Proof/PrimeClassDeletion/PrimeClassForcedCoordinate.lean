/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeAffine

/-! # Exact removal of an actual forced prime coordinate

All cutoffs and ranks are retained. A present coordinate of probability one
shifts the actual prime-class count law by one; an absent coordinate changes
no mass or tail. These identities are algebraic and impose no odds division.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

def removePrimeClass (P : Set Nat) (q : Nat) : Set Nat :=
  fun p => And (Membership.mem P p) (Not (p = q))

theorem primeClassPrefix_erase (P : Set Nat) (X q : Nat) :
    primeClassPrefix (removePrimeClass P q) X = (primeClassPrefix P X).erase q := by
  classical
  apply Finset.ext
  intro p
  simp only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase]
  constructor
  case mp =>
    intro h
    exact And.intro h.2.2.2 (And.intro h.1 (And.intro h.2.1 h.2.2.1))
  case mpr =>
    intro h
    exact And.intro h.2.1 (And.intro h.2.2.1 (And.intro h.2.2.2 h.1))

theorem primeClassPrefix_remove_of_absent (P : Set Nat) (X q : Nat)
    (hq : Not (Membership.mem (primeClassPrefix P X) q)) :
    primeClassPrefix (removePrimeClass P q) X = primeClassPrefix P X := by
  classical
  rw [primeClassPrefix_erase]
  apply Finset.ext
  intro p
  simp only [Finset.mem_erase]
  constructor
  case mp => exact fun h => h.2
  case mpr =>
    intro hp
    refine And.intro ?_ hp
    intro heq
    subst p
    exact hq hp

theorem primeClass_forced_probability_product (P : Set Nat) (eta : Nat -> Real)
    (X q : Nat) (hq : Membership.mem (primeClassPrefix P X) q) (heta : eta q = 1) :
    (primeClassPrefix P X).prod
      (fun p => Polynomial.C (1 - eta p) + Polynomial.C (eta p) * Polynomial.X) =
      Polynomial.X * (primeClassPrefix (removePrimeClass P q) X).prod
        (fun p => Polynomial.C (1 - eta p) + Polynomial.C (eta p) * Polynomial.X) := by
  classical
  let f : Nat -> Polynomial Real :=
    fun p => Polynomial.C (1 - eta p) + Polynomial.C (eta p) * Polynomial.X
  have hprod : (Insert.insert q ((primeClassPrefix P X).erase q)).prod f =
      f q * ((primeClassPrefix P X).erase q).prod f :=
    Finset.prod_insert (by simp)
  rw [Finset.insert_erase hq] at hprod
  have hf : f q = Polynomial.X := by simp [f, heta]
  rw [hf, <- primeClassPrefix_erase P X q] at hprod
  exact hprod

theorem primeClass_forced_mass_zero (P : Set Nat) (eta : Nat -> Real) (X q : Nat)
    (hq : Membership.mem (primeClassPrefix P X) q) (heta : eta q = 1) :
    List.bernoulliOutcomeMass (primeClassCoordinates P eta X) 0 = 0 := by
  rw [primeClassBernoulliMass_eq_product_coeff,
    primeClass_forced_probability_product P eta X q hq heta, Polynomial.coeff_X_mul_zero]

theorem primeClass_forced_mass_succ (P : Set Nat) (eta : Nat -> Real) (X q : Nat)
    (hq : Membership.mem (primeClassPrefix P X) q) (heta : eta q = 1) (r : Nat) :
    List.bernoulliOutcomeMass (primeClassCoordinates P eta X) (r + 1) =
      List.bernoulliOutcomeMass (primeClassCoordinates (removePrimeClass P q) eta X) r := by
  simp only [primeClassBernoulliMass_eq_product_coeff,
    primeClass_forced_probability_product P eta X q hq heta, Polynomial.coeff_X_mul]

theorem primeClassBernoulliTail_sub_succ (P : Set Nat) (eta : Nat -> Real) (X r : Nat) :
    primeClassBernoulliTail P eta X r - primeClassBernoulliTail P eta X (r + 1) =
      List.bernoulliOutcomeMass (primeClassCoordinates P eta X) r := by
  simp only [primeClassBernoulliTail_eq, List.bernoulliOutcomeMass_eq]
  exact List.bernoulliTail_sub_succ _ _

theorem primeClass_forced_tail_succ (P : Set Nat) (eta : Nat -> Real) (X q : Nat)
    (hq : Membership.mem (primeClassPrefix P X) q) (heta : eta q = 1) (r : Nat) :
    primeClassBernoulliTail P eta X (r + 1) =
      primeClassBernoulliTail (removePrimeClass P q) eta X r := by
  induction r with
  | zero =>
      have hd := primeClassBernoulliTail_sub_succ P eta X 0
      have hm := primeClass_forced_mass_zero P eta X q hq heta
      have hp0 : primeClassBernoulliTail P eta X 0 = 1 := by
        simp only [primeClassBernoulliTail_eq, List.bernoulliTail]
      have hr0 : primeClassBernoulliTail (removePrimeClass P q) eta X 0 = 1 := by
        simp only [primeClassBernoulliTail_eq, List.bernoulliTail]
      linarith only [hd, hm, hp0, hr0]
  | succ r ih =>
      have hp := primeClassBernoulliTail_sub_succ P eta X (r + 1)
      have ht := primeClassBernoulliTail_sub_succ (removePrimeClass P q) eta X r
      have hm := primeClass_forced_mass_succ P eta X q hq heta r
      linarith only [hp, ht, hm, ih]

theorem primeClass_removed_mass_eq_of_absent (P : Set Nat) (eta : Nat -> Real)
    (X q : Nat) (hq : Not (Membership.mem (primeClassPrefix P X) q)) (r : Nat) :
    List.bernoulliOutcomeMass (primeClassCoordinates P eta X) r =
      List.bernoulliOutcomeMass (primeClassCoordinates (removePrimeClass P q) eta X) r := by
  simp only [primeClassBernoulliMass_eq_product_coeff]
  rw [primeClassPrefix_remove_of_absent P X q hq]

theorem primeClass_removed_tail_eq_of_absent (P : Set Nat) (eta : Nat -> Real)
    (X q : Nat) (hq : Not (Membership.mem (primeClassPrefix P X) q)) (r : Nat) :
    primeClassBernoulliTail P eta X r =
      primeClassBernoulliTail (removePrimeClass P q) eta X r := by
  simp only [primeClassBernoulliTail_eq, List.bernoulliTail_eq_one_sub_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [List.bernoulliOutcomeMass_eq] using
    primeClass_removed_mass_eq_of_absent P eta X q hq k

theorem affinePrimeEndpoint_rank_shift (rho : Real) (hrho : 0 < rho)
    (P : Set Nat) (X : Nat) (h2 : Membership.mem (primeClassPrefix P X) 2) :
    And (List.bernoulliOutcomeMass
      (primeClassCoordinates P (affinePrimeProbability rho (-2)) X) 0 = 0)
    (And (forall r : Nat, List.bernoulliOutcomeMass
        (primeClassCoordinates P (affinePrimeProbability rho (-2)) X) (r + 1) =
      List.bernoulliOutcomeMass
        (primeClassCoordinates (removePrimeClass P 2) (affinePrimeProbability rho (-2)) X) r)
    (forall r : Nat, primeClassBernoulliTail P (affinePrimeProbability rho (-2)) X (r + 1) =
      primeClassBernoulliTail (removePrimeClass P 2) (affinePrimeProbability rho (-2)) X r)) := by
  have hforced := affinePrimeProbability_endpoint_two rho hrho
  exact And.intro (primeClass_forced_mass_zero P _ X 2 h2 hforced)
    (And.intro (primeClass_forced_mass_succ P _ X 2 h2 hforced)
      (primeClass_forced_tail_succ P _ X 2 h2 hforced))

end PrimeFactorOscillations.PrimeClassDeletion
