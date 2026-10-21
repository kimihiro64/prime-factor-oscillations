/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliDominance
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassRankCoordinates

/-!
# Actual capped-prime coordinates and Bernoulli tail domination

The comparison uses the literal prime ranks and pads only the competing
array by zeros. Deterministic probabilities zero and one remain included.
The same coordinate comparison accepts all finite nonnegative odds.
-/

set_option autoImplicit false
set_option Elab.async false

namespace List

theorem bernoulliCoordinateLE_of_getElem (s t : List Real) :
    s.length = t.length ->
    (forall (i : Nat) (hs : i < s.length) (ht : i < t.length),
      s[i]'hs <= t[i]'ht) ->
    BernoulliCoordinateLE s t := by
  revert t
  induction s with
  | nil =>
    intro t hlen hget
    cases t with
    | nil => exact BernoulliCoordinateLE.nil
    | cons b t =>
      simp only [List.length_nil, List.length_cons] at hlen
      omega
  | cons a s ih =>
    intro t hlen hget
    cases t with
    | nil =>
      simp only [List.length_nil, List.length_cons] at hlen
      omega
    | cons b t =>
      have hab : a <= b :=
        hget 0 (Nat.zero_lt_succ s.length) (Nat.zero_lt_succ t.length)
      have htail : BernoulliCoordinateLE s t := by
        apply ih t (Nat.succ.inj hlen)
        intro i hs ht
        exact hget (i + 1) (Nat.succ_lt_succ hs) (Nat.succ_lt_succ ht)
      exact BernoulliCoordinateLE.cons hab htail

end List

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

theorem primeClassCoordinates_getElem {A : Type*} (P : Set Nat) (f : Nat -> A)
    (X i : Nat) (hi : i < (primeClassPrefix P X).card) :
    (primeClassCoordinates P f X)[i]'(by
      simpa only [primeClassCoordinates_length] using hi) =
        f (primeClassRankValue P i) := by
  unfold primeClassCoordinates
  exact List.getElem_ofFn (by simpa only [List.length_ofFn] using hi)

theorem greedyPrimeClass_local_coordinate_order
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (f : Nat -> Real)
    (hf0 : forall p : Nat, Nat.Prime p -> 0 <= f p)
    (hf : forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p <= q -> f q <= f p) :
    List.BernoulliCoordinateLE
      (primeClassCoordinates P f (Nat.floor x) ++
        List.replicate ((primeClassPrefix greedyPrimeClass (Nat.floor x)).card -
          (primeClassPrefix P (Nat.floor x)).card) (0 : Real))
      (primeClassCoordinates greedyPrimeClass f (Nat.floor x)) := by
  let X := Nat.floor x
  let a := (primeClassPrefix greedyPrimeClass X).card
  let b := (primeClassPrefix P X).card
  have hcount : b <= a := greedyPrimeClass_local_count_optimal P x hx hP
  have hlen :
      (primeClassCoordinates P f X ++ List.replicate (a - b) (0 : Real)).length =
        (primeClassCoordinates greedyPrimeClass f X).length := by
    simp only [List.length_append, List.length_replicate, primeClassCoordinates_length]
    change b + (a - b) = a
    omega
  refine List.bernoulliCoordinateLE_of_getElem _ _ hlen ?_
  intro i hiLeft hiRight
  have hia : i < a := by
    simpa only [primeClassCoordinates_length] using hiRight
  by_cases hib : i < b
  case pos =>
    have hiP : i < (primeClassCoordinates P f X).length := by
      simpa only [primeClassCoordinates_length] using hib
    rw [List.getElem_append_left hiP,
      primeClassCoordinates_getElem P f X i hib,
      primeClassCoordinates_getElem greedyPrimeClass f X i hia]
    exact hf (primeClassRankValue greedyPrimeClass i) (primeClassRankValue P i)
      (primeClassRankValue_spec greedyPrimeClass X i hia).1
      (primeClassRankValue_spec P X i hib).1
      (greedyPrimeClass_local_rankValue_le P x hx hP i hib)
  case neg =>
    have hiP : (primeClassCoordinates P f X).length <= i := by
      rw [primeClassCoordinates_length]
      exact Nat.le_of_not_gt hib
    rw [List.getElem_append_right hiP, List.getElem_replicate,
      primeClassCoordinates_getElem greedyPrimeClass f X i hia]
    exact hf0 (primeClassRankValue greedyPrimeClass i)
      (primeClassRankValue_spec greedyPrimeClass X i hia).1

theorem greedyPrimeClass_local_bernoulli_tail
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (eta : Nat -> Real)
    (heta : forall p : Nat, Nat.Prime p -> And (0 <= eta p) (eta p <= 1))
    (hmono : forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p <= q -> eta q <= eta p)
    (r : Nat) :
    List.bernoulliTail (primeClassCoordinates P eta (Nat.floor x)) r <=
      List.bernoulliTail (primeClassCoordinates greedyPrimeClass eta (Nat.floor x)) r := by
  exact List.bernoulliTail_mono_padded
    (primeClassCoordinates P eta (Nat.floor x))
    (primeClassCoordinates greedyPrimeClass eta (Nat.floor x))
    ((primeClassPrefix greedyPrimeClass (Nat.floor x)).card -
      (primeClassPrefix P (Nat.floor x)).card) r
    (greedyPrimeClass_local_coordinate_order P x hx hP eta (fun p hp => (heta p hp).1) hmono)
    (primeClassCoordinates_unit P eta (Nat.floor x) heta)
    (primeClassCoordinates_unit greedyPrimeClass eta (Nat.floor x) heta)

end PrimeFactorOscillations.PrimeClassDeletion
