/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeClass
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedSelectionWeights

/-!
# Actual weighted extremality and its strict equality case

The signed prefix ledger applies to every nonnegative decreasing prime
weight. A strictly positive, strictly decreasing weight detects every
difference between the two finite selected prime sets.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

theorem primeClassPrefix_sum_eq_selectionCost (P : Set Nat) (w : Nat -> Real) (X : Nat) :
    (primeClassPrefix P X).sum w =
      selectionCost (classPrimeIndices P) (fun i => w (primeAt i)) (primeCutoffLength X) := by
  classical
  calc
    (primeClassPrefix P X).sum w =
        (selectionPrefix (classPrimeIndices P) (primeCutoffLength X)).sum
          (fun i => w (primeAt i)) := by
      rw [primeClassPrefix_eq_indexImage]
      exact Finset.sum_image (fun i _ j _ hij => primeAt_strictMono.injective hij)
    _ = _ := by rw [selectionCost_eq_sum_selectionPrefix]

theorem boundedPrimeClass_greedy_prefix_dominance
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (k : Nat) :
    selectionCount (classPrimeIndices (boundedPrimeClass P (Nat.floor x))) k <=
      selectionCount greedyPrimeIndices k :=
  (greedySelection_prefix_majorization
    (classPrimeIndices (boundedPrimeClass P (Nat.floor x))) primeLogWeight
    (fun i => (primeAt i : Real)) primeLogWeight_monotone
    (primeClass_cap_implies_index_feasible _
      (boundedPrimeClass_nat_cap_of_local_real P x hx hP)) k).1

theorem greedyPrimeClass_local_weight_dominance
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (w : Nat -> Real)
    (hw0 : forall p : Nat, Nat.Prime p -> 0 <= w p)
    (hw : forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p <= q -> w q <= w p) :
    (primeClassPrefix P (Nat.floor x)).sum w <=
      (primeClassPrefix greedyPrimeClass (Nat.floor x)).sum w := by
  let X := Nat.floor x
  let Q := boundedPrimeClass P X
  let n := primeCutoffLength X
  have hb := selectionCost_le_of_prefix_dominance greedyPrimeIndices
    (classPrimeIndices Q) (fun i => w (primeAt i)) n
    (fun k _ => boundedPrimeClass_greedy_prefix_dominance P x hx hP k)
    (hw0 (primeAt n) (prime_primeAt n))
    (fun k _ => hw (primeAt k) (primeAt (k + 1))
      (prime_primeAt k) (prime_primeAt (k + 1))
      (primeAt_strictMono.monotone (Nat.le_succ k)))
  have heq : primeClassPrefix Q X = primeClassPrefix P X :=
    primeClassPrefix_bounded_eq_of_le P X X le_rfl
  rw [<- heq, primeClassPrefix_sum_eq_selectionCost Q w X,
    primeClassPrefix_sum_eq_selectionCost greedyPrimeClass w X,
    classPrimeIndices_greedyPrimeClass]
  exact hb

theorem greedyPrimeClass_local_weight_tie_forces_eq
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (w : Nat -> Real)
    (hw0 : forall p : Nat, Nat.Prime p -> 0 < w p)
    (hw : forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p < q -> w q < w p)
    (htie : (primeClassPrefix greedyPrimeClass (Nat.floor x)).sum w =
      (primeClassPrefix P (Nat.floor x)).sum w) :
    primeClassPrefix greedyPrimeClass (Nat.floor x) = primeClassPrefix P (Nat.floor x) := by
  classical
  let X := Nat.floor x
  let Q := boundedPrimeClass P X
  let n := primeCutoffLength X
  have hprefix : primeClassPrefix Q X = primeClassPrefix P X :=
    primeClassPrefix_bounded_eq_of_le P X X le_rfl
  have hcost : selectionCost greedyPrimeIndices (fun i => w (primeAt i)) n =
      selectionCost (classPrimeIndices Q) (fun i => w (primeAt i)) n := by
    change (primeClassPrefix greedyPrimeClass X).sum w =
      (primeClassPrefix P X).sum w at htie
    rw [<- hprefix, primeClassPrefix_sum_eq_selectionCost greedyPrimeClass w X,
      primeClassPrefix_sum_eq_selectionCost Q w X,
      classPrimeIndices_greedyPrimeClass] at htie
    exact htie
  have heq := selection_eq_of_strict_cost_tie greedyPrimeIndices
    (classPrimeIndices Q) (fun i => w (primeAt i)) n
    (fun k _ => boundedPrimeClass_greedy_prefix_dominance P x hx hP k)
    (hw0 (primeAt n) (prime_primeAt n))
    (fun k _ => hw (primeAt k) (primeAt (k + 1))
      (prime_primeAt k) (prime_primeAt (k + 1))
      (primeAt_strictMono (Nat.lt_succ_self k))) hcost
  have hsets : selectionPrefix greedyPrimeIndices n =
      selectionPrefix (classPrimeIndices Q) n := by
    apply Finset.ext
    intro i
    simp only [selectionPrefix, Finset.mem_filter, Finset.mem_range]
    constructor
    case mp =>
      intro hi
      exact And.intro hi.1 ((heq i hi.1).mp hi.2)
    case mpr =>
      intro hi
      exact And.intro hi.1 ((heq i hi.1).mpr hi.2)
  change primeClassPrefix greedyPrimeClass X = primeClassPrefix P X
  rw [<- hprefix, primeClassPrefix_eq_indexImage greedyPrimeClass X,
    primeClassPrefix_eq_indexImage Q X, classPrimeIndices_greedyPrimeClass]
  exact congrArg (fun S : Finset Nat => S.image primeAt) hsets

theorem greedyPrimeClass_local_rank_complete
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t) :
    (primeClassPrefix P (Nat.floor x)).card <=
      (primeClassPrefix greedyPrimeClass (Nat.floor x)).card /\
    (primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card <=
      (primeClassPrefix (fun p => Not (Membership.mem P p)) (Nat.floor x)).card /\
    (forall p : Nat, Nat.Prime p -> Membership.mem P p -> (p : Real) <= x ->
      exists s : Nat, And (Nat.Prime s) (And (Membership.mem greedyPrimeClass s)
        (And (s <= p)
          ((primeClassPrefix greedyPrimeClass (s - 1)).card =
            (primeClassPrefix P (p - 1)).card)))) /\
    (forall w : Nat -> Real,
      (forall p : Nat, Nat.Prime p -> 0 <= w p) ->
      (forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p <= q -> w q <= w p) ->
      (primeClassPrefix P (Nat.floor x)).sum w <=
        (primeClassPrefix greedyPrimeClass (Nat.floor x)).sum w) /\
    (forall w : Nat -> Real,
      (forall p : Nat, Nat.Prime p -> 0 < w p) ->
      (forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p < q -> w q < w p) ->
      (primeClassPrefix greedyPrimeClass (Nat.floor x)).sum w =
        (primeClassPrefix P (Nat.floor x)).sum w ->
      primeClassPrefix greedyPrimeClass (Nat.floor x) = primeClassPrefix P (Nat.floor x)) := by
  exact And.intro (greedyPrimeClass_local_count_optimal P x hx hP)
    (And.intro (greedyDeletedPrimeClass_local_count_optimal P x hx hP)
      (And.intro (greedyPrimeClass_local_rank_witness P x hx hP)
        (And.intro (greedyPrimeClass_local_weight_dominance P x hx hP)
          (greedyPrimeClass_local_weight_tie_forces_eq P x hx hP))))

end PrimeFactorOscillations.PrimeClassDeletion
