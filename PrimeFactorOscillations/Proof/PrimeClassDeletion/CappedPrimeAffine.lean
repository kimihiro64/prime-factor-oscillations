/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.AffinePrimeLocalLaws

/-! # Actual affine and ordinary-divisibility probability consumers

The probability domain includes beta=-2. The finite odds comparison retains
the strict domain beta>-2; a forced coordinate must be removed before odds
division. These are local prime-coordinate laws, with no extra sampling limit
asserted for an affine polynomial family.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

def PrimeClassProbabilityExtremality (P : Set Nat) (x : Real) (eta : Nat -> Real) : Prop :=
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
      primeClassBernoulliExpectation P eta (Nat.floor x) (fun r => z ^ r))))

theorem greedyPrimeClass_local_affine_probability
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (rho beta : Real) (hrho : 0 < rho) (hbeta : -2 <= beta) :
    PrimeClassProbabilityExtremality P x (affinePrimeProbability rho beta) := by
  exact greedyPrimeClass_local_probability_complete P x hx hP
    (affinePrimeProbability rho beta)
    (affinePrimeProbability_unit rho beta hrho hbeta)
    (affinePrimeProbability_antitone rho beta hrho hbeta)

theorem greedyPrimeClass_local_affine_odds_coefficient
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (rho beta : Real) (hrho : 0 < rho) (hbeta : -2 < beta) (r : Nat) :
    ((primeClassPrefix P (Nat.floor x)).prod
      (fun p => 1 + Polynomial.C (affinePrimeOdds rho beta p) * Polynomial.X)).coeff r <=
    ((primeClassPrefix greedyPrimeClass (Nat.floor x)).prod
      (fun p => 1 + Polynomial.C (affinePrimeOdds rho beta p) * Polynomial.X)).coeff r := by
  exact greedyPrimeClass_local_odds_coefficient P x hx hP (affinePrimeOdds rho beta)
    (affinePrimeOdds_nonneg rho beta hrho hbeta)
    (affinePrimeOdds_antitone rho beta hrho hbeta) r

theorem greedyPrimeClass_local_ordinary_probability
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t) :
    PrimeClassProbabilityExtremality P x (fun p => 1 / (p : Real)) := by
  have heq : affinePrimeProbability 1 (-1) = (fun p : Nat => 1 / (p : Real)) := by
    funext p
    exact affinePrimeProbability_ordinary p
  rw [<- heq]
  exact greedyPrimeClass_local_affine_probability P x hx hP 1 (-1) (by norm_num) (by norm_num)

theorem greedyPrimeClass_local_ordinary_odds_coefficient
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (r : Nat) :
    ((primeClassPrefix P (Nat.floor x)).prod
      (fun p => 1 + Polynomial.C (1 / ((p : Real) - 1)) * Polynomial.X)).coeff r <=
    ((primeClassPrefix greedyPrimeClass (Nat.floor x)).prod
      (fun p => 1 + Polynomial.C (1 / ((p : Real) - 1)) * Polynomial.X)).coeff r := by
  simpa only [affinePrimeOdds_ordinary] using
    greedyPrimeClass_local_affine_odds_coefficient P x hx hP 1 (-1)
      (by norm_num) (by norm_num) r

end PrimeFactorOscillations.PrimeClassDeletion
