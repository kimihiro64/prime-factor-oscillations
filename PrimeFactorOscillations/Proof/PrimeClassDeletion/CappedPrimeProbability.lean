/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliFiniteObservables
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliProbabilityProduct
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeExpectations
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeOdds

/-! # Complete finite probability extremality of the greedy capped prime class

The observables are evaluated on the actual finite product space of bits,
whose weights are nonnegative and sum to one. The competing cap is local
to the chosen real cutoff. Arbitrary increasing tests may have either sign.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

noncomputable def primeClassBernoulliExpectation (P : Set Nat) (eta : Nat -> Real)
    (X : Nat) (phi : Nat -> Real) : Real :=
  Finset.univ.sum (fun w : List.BernoulliOutcomes (primeClassCoordinates P eta X).length =>
    phi (List.bernoulliOutcomeCount w) *
      List.bernoulliOutcomeWeight (primeClassCoordinates P eta X) w)

noncomputable def primeClassBernoulliTail (P : Set Nat) (eta : Nat -> Real)
    (X r : Nat) : Real :=
  List.bernoulliOutcomeTail (primeClassCoordinates P eta X) r

theorem primeClassBernoulliExpectation_eq (P : Set Nat) (eta : Nat -> Real)
    (X : Nat) (phi : Nat -> Real) :
    primeClassBernoulliExpectation P eta X phi =
      List.bernoulliExpectation (primeClassCoordinates P eta X) phi := by
  exact List.bernoulliOutcomeExpectation_eq _ _

theorem primeClassBernoulliTail_eq (P : Set Nat) (eta : Nat -> Real) (X r : Nat) :
    primeClassBernoulliTail P eta X r =
      List.bernoulliTail (primeClassCoordinates P eta X) r := by
  exact List.bernoulliOutcomeTail_eq _ _

theorem primeClassBernoulliLaw_valid (P : Set Nat) (eta : Nat -> Real) (X : Nat)
    (heta : forall p : Nat, Nat.Prime p -> And (0 <= eta p) (eta p <= 1)) :
    And (forall w : List.BernoulliOutcomes (primeClassCoordinates P eta X).length,
      0 <= List.bernoulliOutcomeWeight (primeClassCoordinates P eta X) w)
      ((Finset.univ.sum
        (fun w : List.BernoulliOutcomes (primeClassCoordinates P eta X).length =>
          List.bernoulliOutcomeWeight (primeClassCoordinates P eta X) w)) = 1) := by
  exact And.intro
    (List.bernoulliOutcomeWeight_nonneg _ (primeClassCoordinates_unit P eta X heta))
    (List.bernoulliOutcomeWeight_sum _)

theorem primeClassCoordinates_probability_product (P : Set Nat) (eta : Nat -> Real)
    (X : Nat) :
    List.bernoulliProbabilityProduct (primeClassCoordinates P eta X) =
      (primeClassPrefix P X).prod
        (fun p => Polynomial.C (1 - eta p) + Polynomial.C (eta p) * Polynomial.X) := by
  rw [List.bernoulliProbabilityProduct, primeClassCoordinates_map, primeClassCoordinates_prod]

theorem primeClassBernoulliMass_eq_product_coeff (P : Set Nat) (eta : Nat -> Real)
    (X r : Nat) :
    List.bernoulliOutcomeMass (primeClassCoordinates P eta X) r =
      ((primeClassPrefix P X).prod
        (fun p => Polynomial.C (1 - eta p) + Polynomial.C (eta p) * Polynomial.X)).coeff r := by
  rw [<- primeClassCoordinates_probability_product, List.bernoulliProbabilityProduct_coeff,
    List.bernoulliOutcomeMass_eq]

theorem greedyPrimeClass_local_probability_complete
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (eta : Nat -> Real)
    (heta : forall p : Nat, Nat.Prime p -> And (0 <= eta p) (eta p <= 1))
    (hmono : forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p <= q -> eta q <= eta p) :
    And (forall r : Nat,
      primeClassBernoulliTail P eta (Nat.floor x) r <=
        primeClassBernoulliTail greedyPrimeClass eta (Nat.floor x) r)
    (And (forall phi : Nat -> Real,
      (forall k, k < (primeClassPrefix greedyPrimeClass (Nat.floor x)).card ->
        phi k <= phi (k + 1)) ->
      primeClassBernoulliExpectation P eta (Nat.floor x) phi <=
        primeClassBernoulliExpectation greedyPrimeClass eta (Nat.floor x) phi)
    (And (forall z : Real, 1 <= z ->
      primeClassBernoulliExpectation P eta (Nat.floor x) (fun r => z ^ r) <=
        primeClassBernoulliExpectation greedyPrimeClass eta (Nat.floor x) (fun r => z ^ r))
    (forall z : Real, 0 <= z -> z <= 1 ->
      primeClassBernoulliExpectation greedyPrimeClass eta (Nat.floor x) (fun r => z ^ r) <=
        primeClassBernoulliExpectation P eta (Nat.floor x) (fun r => z ^ r)))) := by
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  next =>
    intro r
    simp only [primeClassBernoulliTail_eq]
    exact greedyPrimeClass_local_bernoulli_tail P x hx hP eta heta hmono r
  next =>
    intro phi hphi
    simp only [primeClassBernoulliExpectation_eq]
    exact greedyPrimeClass_local_bernoulli_expectation P x hx hP eta heta hmono phi hphi
  next =>
    intro z hz
    simp only [primeClassBernoulliExpectation_eq]
    exact greedyPrimeClass_local_bernoulli_moment_ge_one P x hx hP eta heta hmono z hz
  next =>
    intro z hz0 hz1
    simp only [primeClassBernoulliExpectation_eq]
    exact greedyPrimeClass_local_bernoulli_moment_unit P x hx hP eta heta hmono z hz0 hz1

end PrimeFactorOscillations.PrimeClassDeletion
