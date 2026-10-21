/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliExpectations
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeCoordinateOrder

/-! # Every increasing test and both moment ranges for capped prime classes -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

theorem greedyPrimeClass_local_bernoulli_expectation
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (eta : Nat -> Real)
    (heta : forall p : Nat, Nat.Prime p -> And (0 <= eta p) (eta p <= 1))
    (hmono : forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p <= q -> eta q <= eta p)
    (phi : Nat -> Real)
    (hphi : forall k, k < (primeClassPrefix greedyPrimeClass (Nat.floor x)).card ->
      phi k <= phi (k + 1)) :
    List.bernoulliExpectation (primeClassCoordinates P eta (Nat.floor x)) phi <=
      List.bernoulliExpectation
        (primeClassCoordinates greedyPrimeClass eta (Nat.floor x)) phi := by
  have hlen : (primeClassCoordinates P eta (Nat.floor x)).length <=
      (primeClassCoordinates greedyPrimeClass eta (Nat.floor x)).length := by
    simpa only [primeClassCoordinates_length] using
      greedyPrimeClass_local_count_optimal P x hx hP
  exact List.bernoulliExpectation_le_of_tails _ _ hlen
    (greedyPrimeClass_local_bernoulli_tail P x hx hP eta heta hmono) phi
    (by simpa only [primeClassCoordinates_length] using hphi)

theorem greedyPrimeClass_local_bernoulli_moment_ge_one
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (eta : Nat -> Real)
    (heta : forall p : Nat, Nat.Prime p -> And (0 <= eta p) (eta p <= 1))
    (hmono : forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p <= q -> eta q <= eta p)
    (z : Real) (hz : 1 <= z) :
    List.bernoulliExpectation (primeClassCoordinates P eta (Nat.floor x)) (fun r => z ^ r) <=
      List.bernoulliExpectation
        (primeClassCoordinates greedyPrimeClass eta (Nat.floor x)) (fun r => z ^ r) := by
  have hlen : (primeClassCoordinates P eta (Nat.floor x)).length <=
      (primeClassCoordinates greedyPrimeClass eta (Nat.floor x)).length := by
    simpa only [primeClassCoordinates_length] using
      greedyPrimeClass_local_count_optimal P x hx hP
  exact List.bernoulliExpectation_pow_le_of_one_le _ _ hlen
    (greedyPrimeClass_local_bernoulli_tail P x hx hP eta heta hmono) z hz

theorem greedyPrimeClass_local_bernoulli_moment_unit
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (eta : Nat -> Real)
    (heta : forall p : Nat, Nat.Prime p -> And (0 <= eta p) (eta p <= 1))
    (hmono : forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p <= q -> eta q <= eta p)
    (z : Real) (hz0 : 0 <= z) (hz1 : z <= 1) :
    List.bernoulliExpectation
        (primeClassCoordinates greedyPrimeClass eta (Nat.floor x)) (fun r => z ^ r) <=
      List.bernoulliExpectation (primeClassCoordinates P eta (Nat.floor x)) (fun r => z ^ r) := by
  have hlen : (primeClassCoordinates P eta (Nat.floor x)).length <=
      (primeClassCoordinates greedyPrimeClass eta (Nat.floor x)).length := by
    simpa only [primeClassCoordinates_length] using
      greedyPrimeClass_local_count_optimal P x hx hP
  exact List.bernoulliExpectation_pow_le_of_mem_unit _ _ hlen
    (greedyPrimeClass_local_bernoulli_tail P x hx hP eta heta hmono) z hz0 hz1

end PrimeFactorOscillations.PrimeClassDeletion
