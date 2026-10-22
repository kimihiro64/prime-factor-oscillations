/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentGeometric

/-!
# Independent geometric valuations, with finite support almost surely

The infinite component law has the exact product joint masses on every
finite prime set. Its integer realization has only finitely many nonzero
valuation coordinates, an event of total reference probability one.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

noncomputable def primeValuationCylinderMass
    (mass : Nat -> Real) (s : Finset Nat) (k : Nat -> Nat) : Real :=
  tsum (fun a : {a : Nat //
    forall p : Nat, Membership.mem s p -> a.factorization p = k p} => mass a.val)

theorem primeValuationCylinderMass_eq_componentStatisticMass
    (mass : Nat -> Real) (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) (k : Nat -> Nat) :
    primeValuationCylinderMass mass s k =
      componentStatisticMass (finitePrimePowerComponent s) mass
        (finitePrimeValuationAtom s k) := by
  let e : Equiv
      {a : Nat // forall p : Nat, Membership.mem s p -> a.factorization p = k p}
      {a : Nat // finitePrimePowerComponent s a = finitePrimeValuationAtom s k} :=
    { toFun := fun a => Subtype.mk a.val
        ((finitePrimePowerComponent_eq_valuationAtom_iff s hprime k a.val).mpr a.property)
      invFun := fun a => Subtype.mk a.val
        ((finitePrimePowerComponent_eq_valuationAtom_iff s hprime k a.val).mp a.property)
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
  exact e.tsum_eq (fun a => mass a.val)

theorem classPrimePowerReference_valuationCylinder
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1))
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hP : forall p : Nat, Membership.mem s p -> Membership.mem P p) (k : Nat -> Nat) :
    primeValuationCylinderMass (classPrimePowerReference P) s k =
      s.prod (fun p => (1 - 1 / (p : Real)) / (p : Real) ^ k p) := by
  rw [primeValuationCylinderMass_eq_componentStatisticMass _ s hprime k,
    classPrimePowerReference_subprojection P hsum s hprime hP,
    finitePrimePowerReference_valuationAtom s hprime k]

theorem classPrimePowerReference_valuation
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1))
    (p : Nat) (hp : Nat.Prime p) (hP : Membership.mem P p) (k : Nat) :
    primeValuationCylinderMass (classPrimePowerReference P) {p} (fun _ => k) =
      (1 - 1 / (p : Real)) / (p : Real) ^ k := by
  have hprime : forall q : Nat, Membership.mem ({p} : Finset Nat) q -> Nat.Prime q := by
    intro q hq
    have heq := Finset.mem_singleton.mp hq
    subst q
    exact hp
  have hclass : forall q : Nat,
      Membership.mem ({p} : Finset Nat) q -> Membership.mem P q := by
    intro q hq
    have heq := Finset.mem_singleton.mp hq
    subst q
    exact hP
  simpa only [Finset.prod_singleton] using
    classPrimePowerReference_valuationCylinder P hsum {p} hprime hclass (fun _ => k)

theorem classPrimePowerReference_valuations_independent
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1))
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hP : forall p : Nat, Membership.mem s p -> Membership.mem P p) (k : Nat -> Nat) :
    primeValuationCylinderMass (classPrimePowerReference P) s k =
      s.prod (fun p => primeValuationCylinderMass
        (classPrimePowerReference P) {p} (fun _ => k p)) := by
  rw [classPrimePowerReference_valuationCylinder P hsum s hprime hP k]
  apply Finset.prod_congr rfl
  intro p hp
  exact (classPrimePowerReference_valuation P hsum p (hprime p hp) (hP p hp) (k p)).symm

theorem primeValuation_finite_support (a : Nat) :
    Set.Finite {p : Nat | Not (a.factorization p = 0)} := by
  apply a.factorization.support.finite_toSet.subset
  intro p hp
  exact Finsupp.mem_support_iff.mpr hp

theorem classPrimePowerReference_valuation_finite_support_mass_one
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) :
    tsum (fun a : {a : Nat // Set.Finite {p : Nat | Not (a.factorization p = 0)}} =>
      classPrimePowerReference P a.val) = 1 := by
  let e : Equiv Nat
      {a : Nat // Set.Finite {p : Nat | Not (a.factorization p = 0)}} :=
    { toFun := fun a => Subtype.mk a (primeValuation_finite_support a)
      invFun := Subtype.val
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
  have he : tsum (classPrimePowerReference P) =
      tsum (fun a : {a : Nat // Set.Finite {p : Nat | Not (a.factorization p = 0)}} =>
        classPrimePowerReference P a.val) :=
    e.tsum_eq (fun a => classPrimePowerReference P a.val)
  exact he.symm.trans (classPrimePowerReference_hasSum_one P hsum).tsum_eq

end PrimeFactorOscillations.PrimeClassSampling
