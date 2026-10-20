/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.QuotientRing
import PrimeFactorOscillations.Helpers.CyclotomicProbability

/-!
# Exact finite-cutoff cyclotomic sampling law

Uniform sampling of one scalar modulo the product of a finite set of divisor
primes gives the full independent Bernoulli vector for Phi_q. Every success
and failure pattern is counted, including empty prime sets and depleted
primes. The modulus q and the finite divisor support are fixed parameters.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CyclotomicProbability

local instance (p : Nat.Primes) : NeZero (p : Nat) :=
  NeZero.mk p.property.ne_zero

/-- Actual modular roots, with the ramified primes explicitly omitted. -/
def successSet (q : Nat) (p : Nat.Primes) : Finset (ZMod (p : Nat)) := by
  classical
  exact (GeneralPolynomialLaw.rootSet (Polynomial.cyclotomic q Int) p).filter
    (fun _ => Not (Dvd.dvd (p : Nat) q))

theorem successSet_card (q : Nat) (p : Nat.Primes) :
    (successSet q p).card = count q p := by
  classical
  by_cases hpq : Dvd.dvd (p : Nat) q
  { simp [successSet, count, hpq] }
  { simp [successSet, count, hpq, GeneralPolynomialLaw.rootCount] }

theorem successSet_mem (q : Nat) (p : Nat.Primes) (x : ZMod (p : Nat)) :
    Membership.mem (successSet q p) x <->
      And (Not (Dvd.dvd (p : Nat) q))
        ((GeneralPolynomialLaw.reduction (Polynomial.cyclotomic q Int) p).eval x = 0) := by
  classical
  simp only [successSet, GeneralPolynomialLaw.rootSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact and_comm

/-- The local outcomes for either a success or a failure. -/
def patternSet (q : Nat) (p : Nat.Primes) (bit : Bool) :
    Finset (ZMod (p : Nat)) := by
  classical
  exact if bit then successSet q p
    else Finset.univ.filter (fun x => Not (Membership.mem (successSet q p) x))

theorem patternSet_card (q : Nat) (p : Nat.Primes) (bit : Bool) :
    (patternSet q p bit).card =
      if bit then count q p else (p : Nat) - count q p := by
  classical
  cases bit
  { change (Finset.univ.filter
      (fun x : ZMod (p : Nat) => Not (Membership.mem (successSet q p) x))).card =
        (p : Nat) - count q p
    have hs :
        Finset.univ.filter (fun x : ZMod (p : Nat) =>
          Membership.mem (successSet q p) x) = successSet q p := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ZMod (p : Nat))))
      (fun x => Membership.mem (successSet q p) x)
    rw [hs, successSet_card, Finset.card_univ, ZMod.card] at h
    omega }
  { exact successSet_card q p }

/-- One scalar sampling period for a finite divisor support. -/
def sampleModulus (S : Finset Nat.Primes) : Nat :=
  Finset.prod (Finset.univ : Finset S) (fun p => (p.val : Nat))

local instance (S : Finset Nat.Primes) : NeZero (sampleModulus S) :=
  NeZero.mk (by
    unfold sampleModulus
    apply Finset.prod_ne_zero_iff.mpr
    intro p _
    exact p.val.property.ne_zero)

/-- The canonical Chinese remainder equivalence for the actual scalar. -/
def residueEquiv (S : Finset Nat.Primes) :
    RingEquiv (ZMod (sampleModulus S)) ((p : S) -> ZMod (p.val : Nat)) :=
  ZMod.prodEquivPi (fun p : S => (p.val : Nat)) (by
    intro p r hne
    apply (Nat.coprime_primes p.val.property r.val.property).mpr
    intro h
    apply hne
    apply Subtype.ext
    exact Subtype.ext h)

theorem residueEquiv_natCast (S : Finset Nat.Primes) (u : Nat) (p : S) :
    residueEquiv S (u : ZMod (sampleModulus S)) p =
      (u : ZMod (p.val : Nat)) := by
  exact congrFun (map_natCast (residueEquiv S) u) p

/-- All scalar residues giving the specified full binary outcome pattern. -/
def jointSet (q : Nat) (S : Finset Nat.Primes) (bits : S -> Bool) :
    Finset (ZMod (sampleModulus S)) := by
  classical
  exact (Fintype.piFinset (fun p : S => patternSet q p.val (bits p))).map
    (residueEquiv S).symm.toEquiv.toEmbedding

theorem jointSet_mem (q : Nat) (S : Finset Nat.Primes) (bits : S -> Bool)
    (u : ZMod (sampleModulus S)) :
    Membership.mem (jointSet q S bits) u <->
      forall p : S, Membership.mem (patternSet q p.val (bits p)) (residueEquiv S u p) := by
  classical
  constructor
  { intro hu
    choose v hv using Finset.mem_map.mp hu
    intro p
    have heq : residueEquiv S u p = v p := by
      rw [<- hv.2]
      exact congrFun ((residueEquiv S).apply_symm_apply v) p
    rw [heq]
    exact Fintype.mem_piFinset.mp hv.1 p }
  { intro hu
    exact Finset.mem_map.mpr (Exists.intro (residueEquiv S u)
      (And.intro (Fintype.mem_piFinset.mpr hu) ((residueEquiv S).symm_apply_apply u))) }

/-- Exact signed-pattern numerator, with no asymptotic or sampling error. -/
theorem jointSet_card (q : Nat) (S : Finset Nat.Primes) (bits : S -> Bool) :
    (jointSet q S bits).card =
      Finset.prod Finset.univ (fun p : S =>
        if bits p then count q p.val else (p.val : Nat) - count q p.val) := by
  classical
  unfold jointSet
  rw [Finset.card_map, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro p _
  exact patternSet_card q p.val (bits p)

/-- The probability under uniform scalar sampling over one complete period. -/
def jointProbability (q : Nat) (S : Finset Nat.Primes) (bits : S -> Bool) : Real :=
  ((jointSet q S bits).card : Real) / Fintype.card (ZMod (sampleModulus S))

/-- Full Bernoulli independence at every fixed finite divisor support. -/
theorem jointProbability_eq_product (q : Nat) (S : Finset Nat.Primes)
    (bits : S -> Bool) :
    jointProbability q S bits =
      Finset.prod Finset.univ (fun p : S =>
        if bits p then probability q p.val else 1 - probability q p.val) := by
  classical
  unfold jointProbability
  rw [jointSet_card, ZMod.card]
  simp only [sampleModulus, Nat.cast_prod]
  rw [<- Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  cases he : bits p
  { change ((((p.val : Nat) - count q p.val : Nat) : Real) /
      ((p.val : Nat) : Real)) = 1 - probability q p.val
    rw [Nat.cast_sub (count_lt_prime q p.val).le, sub_div]
    have hp : Not (((p.val : Nat) : Real) = 0) := by
      exact_mod_cast p.val.property.ne_zero
    rw [div_self hp]
    rfl }
  { rfl }

end PrimeFactorOscillations.CyclotomicProbability
