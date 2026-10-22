/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeComponentLaw
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeEulerSummability
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentIndependence

/-!
# The actual deleted-prime geometric law

The proved reciprocal summability of the actual greedy deleted-prime
class supplies every hypothesis of the geometric reference law.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeClassSampling

theorem greedyDeletedPrimeClass_valuationCylinder
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hD : forall p : Nat, Membership.mem s p -> Membership.mem greedyDeletedPrimeClass p)
    (k : Nat -> Nat) :
    primeValuationCylinderMass (classPrimePowerReference greedyDeletedPrimeClass) s k =
      s.prod (fun p => (1 - 1 / (p : Real)) / (p : Real) ^ k p) := by
  exact classPrimePowerReference_valuationCylinder greedyDeletedPrimeClass
    greedyDeletedPrimeClass_reciprocal_summable s hprime hD k

theorem greedyDeletedPrimeClass_valuations_independent
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hD : forall p : Nat, Membership.mem s p -> Membership.mem greedyDeletedPrimeClass p)
    (k : Nat -> Nat) :
    primeValuationCylinderMass (classPrimePowerReference greedyDeletedPrimeClass) s k =
      s.prod (fun p => primeValuationCylinderMass
        (classPrimePowerReference greedyDeletedPrimeClass) {p} (fun _ => k p)) := by
  exact classPrimePowerReference_valuations_independent greedyDeletedPrimeClass
    greedyDeletedPrimeClass_reciprocal_summable s hprime hD k

theorem greedyDeletedPrimeClass_valuation_finite_support_mass_one :
    tsum (fun a : {a : Nat // Set.Finite {p : Nat | Not (a.factorization p = 0)}} =>
      classPrimePowerReference greedyDeletedPrimeClass a.val) = 1 := by
  exact classPrimePowerReference_valuation_finite_support_mass_one greedyDeletedPrimeClass
    greedyDeletedPrimeClass_reciprocal_summable

end PrimeFactorOscillations.PrimeClassDeletion
