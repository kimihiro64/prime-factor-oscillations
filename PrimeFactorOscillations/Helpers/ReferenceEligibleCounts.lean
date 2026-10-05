/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.AscentEndpoints
import PrimeFactorOscillations.Helpers.PrimeProfileAscentEligibility

/-!
# Exact capacity from early and reference-eligible prime endpoints

A separated reversal family injects into distinct lower ascent primes. Split
those primes at the real lower cutoff and retain the actual consecutive-gap
reference test in a finite upper window. The resulting count inequality is
exact, including its floor and strict upper-endpoint conventions.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

def ordinaryReferenceEligible (k i : Nat) : Prop :=
  let L := Real.eulerMascheroniConstant + Real.log (Real.log
    (Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real)))
  (PrimeFactorUnimodality.primeGap i : Real) + 1 <
    Nat.factorialConvolution primeProfileRealCoefficient (k - 2) L /
      Nat.factorialConvolution primeProfileRealCoefficient (k - 1) L

noncomputable def ordinaryReferenceEligiblePrimes (k : Nat) (X : Real) (U : Nat) : Finset Nat := by
  classical
  exact (Finset.range U).filter (fun p : Nat =>
    Nat.Prime p /\ X <= (p : Real) /\ exists i : Nat,
      PrimeFactorUnimodality.primeAt i = p /\ ordinaryReferenceEligible k i)

noncomputable def ordinaryReferenceEligibleCount (k : Nat) (X : Real) (U : Nat) : Nat :=
  (ordinaryReferenceEligiblePrimes k X U).card

theorem mem_ordinaryReferenceEligiblePrimes (k : Nat) (X : Real) (U p : Nat) :
    Membership.mem (ordinaryReferenceEligiblePrimes k X U) p <->
      p < U /\ Nat.Prime p /\ X <= (p : Real) /\ exists i : Nat,
        PrimeFactorUnimodality.primeAt i = p /\ ordinaryReferenceEligible k i := by
  classical
  simp only [ordinaryReferenceEligiblePrimes, Finset.mem_filter, Finset.mem_range]

theorem reversal_count_le_reference_eligible {R : Type*} [Preorder R]
    (f : Nat -> R) (k m : Nat) (X : Real) (U : Nat)
    (hlate : forall i : Nat, f i < f (i + 1) ->
      X <= (PrimeFactorUnimodality.primeAt i : Real) ->
        PrimeFactorUnimodality.primeAt i < U /\ ordinaryReferenceEligible k i)
    (hm : HasAtLeastReversals f m) :
    m <= Nat.primeCounting (Nat.floor X) + ordinaryReferenceEligibleCount k X U := by
  classical
  let S : Finset Nat := Union.union (Nat.primesLE (Nat.floor X))
    (ordinaryReferenceEligiblePrimes k X U)
  have hcover (i : Nat) (hi : f i < f (i + 1)) :
      Membership.mem S (PrimeFactorUnimodality.primeAt i) := by
    apply Finset.mem_union.mpr
    by_cases hp : (PrimeFactorUnimodality.primeAt i : Real) <= X
    case pos =>
      exact Or.inl (Nat.mem_primesLE.mpr (And.intro
        (Nat.le_floor hp) (PrimeFactorUnimodality.prime_primeAt i)))
    case neg =>
      have hX : X <= (PrimeFactorUnimodality.primeAt i : Real) := (lt_of_not_ge hp).le
      have h := hlate i hi hX
      apply Or.inr
      apply (mem_ordinaryReferenceEligiblePrimes k X U _).mpr
      exact And.intro h.1 (And.intro (PrimeFactorUnimodality.prime_primeAt i)
        (And.intro hX (Exists.intro i (And.intro rfl h.2))))
  have hc := reversal_count_le_prime_endpoint_card f m (S : Set Nat) S.finite_toSet hcover hm
  change m <= Nat.card {p : Nat // Membership.mem S p} at hc
  have hbound : m <= S.card := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc
  have hsize : S.card <= Nat.primeCounting (Nat.floor X) +
      ordinaryReferenceEligibleCount k X U := by
    have h : S.card <= (Nat.primesLE (Nat.floor X)).card +
        (ordinaryReferenceEligiblePrimes k X U).card := Finset.card_union_le _ _
    simpa only [Nat.primesLE_card_eq_primeCounting, ordinaryReferenceEligibleCount] using h
  exact hbound.trans hsize

end PrimeFactorOscillations
