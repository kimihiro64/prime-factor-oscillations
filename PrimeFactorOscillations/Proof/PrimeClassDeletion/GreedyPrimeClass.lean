/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassIndexBridge

/-!
# The actual fixed greedy prime class and exact deletion-count optimality

The real-logarithmic greedy rule is instantiated on increasing actual primes.
Literal prime-class theta sums obey the cap at every cutoff. Every other
class with the same cap deletes at least as many primes at each cutoff.
These statements do not assert an algorithm for deciding real comparisons
or any asymptotic estimate for the number of rejected primes.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

noncomputable def greedyPrimeIndices : Nat -> Prop :=
  greedySelection primeLogWeight (fun i => (primeAt i : Real))

noncomputable def greedyPrimeClass : Set Nat :=
  fun p => And (Nat.Prime p) (greedyPrimeIndices (Nat.count Nat.Prime p))

noncomputable def greedyDeletedPrimeClass : Set Nat :=
  fun p => And (Nat.Prime p) (Not (greedyPrimeIndices (Nat.count Nat.Prime p)))

noncomputable def primeClassTheta (P : Set Nat) (X : Nat) : Real :=
  (primeClassPrefix P X).sum (fun p => Real.log (p : Real))

noncomputable def primeClassThetaReal (P : Set Nat) (x : Real) : Real :=
  primeClassTheta P (Nat.floor x)

theorem classPrimeIndices_greedyPrimeClass :
    classPrimeIndices greedyPrimeClass = greedyPrimeIndices := by
  funext i
  apply propext
  change And (Nat.Prime (primeAt i))
    (greedyPrimeIndices (Nat.count Nat.Prime (primeAt i))) <-> greedyPrimeIndices i
  rw [primeCount_primeAt]
  exact and_iff_right (prime_primeAt i)

theorem classPrimeIndices_greedyDeletedPrimeClass :
    classPrimeIndices greedyDeletedPrimeClass = fun i => Not (greedyPrimeIndices i) := by
  funext i
  apply propext
  change And (Nat.Prime (primeAt i))
    (Not (greedyPrimeIndices (Nat.count Nat.Prime (primeAt i)))) <->
      Not (greedyPrimeIndices i)
  rw [primeCount_primeAt]
  exact and_iff_right (prime_primeAt i)

theorem greedyPrimeClass_count_eq (X : Nat) :
    (primeClassPrefix greedyPrimeClass X).card =
      selectionCount greedyPrimeIndices (primeCutoffLength X) := by
  rw [primeClassPrefix_card_eq_selectionCount, classPrimeIndices_greedyPrimeClass]

theorem greedyPrimeClass_theta_eq_cost (X : Nat) :
    primeClassTheta greedyPrimeClass X =
      greedySelectionCost primeLogWeight (fun i => (primeAt i : Real)) (primeCutoffLength X) := by
  unfold primeClassTheta
  rw [primeClassPrefix_logSum_eq_selectionCost, classPrimeIndices_greedyPrimeClass]
  exact selectionCost_greedySelection _ _ _

theorem greedyPrimeClass_prefix_cost_le (n : Nat) :
    greedySelectionCost primeLogWeight (fun i => (primeAt i : Real)) (n + 1) <=
      (primeAt n : Real) := by
  classical
  induction n with
  | zero =>
      change (if 0 + primeLogWeight 0 <= (primeAt 0 : Real) then
        0 + primeLogWeight 0 else 0) <= (primeAt 0 : Real)
      split_ifs with h
      case pos => exact h
      case neg => exact Nat.cast_nonneg _
  | succ n ih =>
      change (if greedySelectionCost primeLogWeight (fun i => (primeAt i : Real)) (n + 1) +
          primeLogWeight (n + 1) <= (primeAt (n + 1) : Real) then
        greedySelectionCost primeLogWeight (fun i => (primeAt i : Real)) (n + 1) +
          primeLogWeight (n + 1) else
        greedySelectionCost primeLogWeight (fun i => (primeAt i : Real)) (n + 1)) <=
          (primeAt (n + 1) : Real)
      split_ifs with h
      case pos => exact h
      case neg =>
        exact ih.trans (Nat.cast_le.mpr (primeAt_strictMono.monotone (Nat.le_succ n)))

theorem greedyPrimeClass_theta_le (X : Nat) :
    primeClassTheta greedyPrimeClass X <= (X : Real) := by
  rw [greedyPrimeClass_theta_eq_cost]
  cases hN : primeCutoffLength X with
  | zero => exact Nat.cast_nonneg X
  | succ n =>
      have hp : primeAt n <= X := (primeAt_le_cutoff_iff n X).mpr (by
        rw [hN]
        exact Nat.lt_succ_self n)
      exact (greedyPrimeClass_prefix_cost_le n).trans (Nat.cast_le.mpr hp)

theorem greedyPrimeClass_thetaReal_le (x : Real) (hx : 0 <= x) :
    primeClassThetaReal greedyPrimeClass x <= x :=
  (greedyPrimeClass_theta_le (Nat.floor x)).trans (Nat.floor_le hx)

theorem primeClass_cap_implies_index_feasible
    (P : Set Nat) (hP : forall X : Nat, primeClassTheta P X <= (X : Real)) :
    forall i : Nat, classPrimeIndices P i ->
      selectionCost (classPrimeIndices P) primeLogWeight i + primeLogWeight i <=
        (primeAt i : Real) := by
  intro i hi
  have hcap := hP (primeAt i)
  have hlength : primeCutoffLength (primeAt i) = i + 1 :=
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime i
  unfold primeClassTheta at hcap
  rw [primeClassPrefix_logSum_eq_selectionCost, hlength] at hcap
  simpa only [selectionCost, ite_eq_left hi] using hcap

theorem greedyPrimeClass_count_optimal
    (P : Set Nat) (hP : forall X : Nat, primeClassTheta P X <= (X : Real)) (X : Nat) :
    (primeClassPrefix P X).card <= (primeClassPrefix greedyPrimeClass X).card := by
  rw [primeClassPrefix_card_eq_selectionCount, greedyPrimeClass_count_eq]
  exact (greedySelection_prefix_majorization (classPrimeIndices P)
    primeLogWeight (fun i => (primeAt i : Real)) primeLogWeight_monotone
    (primeClass_cap_implies_index_feasible P hP) (primeCutoffLength X)).1

theorem selectionCount_not_eq_sub (a : Nat -> Prop) (n : Nat) :
    selectionCount (fun i => Not (a i)) n = n - selectionCount a n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
      have hle := selectionCount_le_length a n
      by_cases ha : a n
      case pos => simp [selectionCount, ha, ih]
      case neg =>
        simp only [selectionCount, ite_eq_right ha, ite_eq_left ha, Nat.add_zero, ih]
        omega

theorem primeClassPrefix_complement_card (P : Set Nat) (X : Nat) :
    (primeClassPrefix (fun p => Not (Membership.mem P p)) X).card =
      primeCutoffLength X - (primeClassPrefix P X).card := by
  rw [primeClassPrefix_card_eq_selectionCount (fun p => Not (Membership.mem P p)) X]
  change selectionCount (fun i => Not (classPrimeIndices P i)) (primeCutoffLength X) = _
  rw [selectionCount_not_eq_sub, primeClassPrefix_card_eq_selectionCount P X]

theorem greedyDeletedPrimeClass_count_eq_sub (X : Nat) :
    (primeClassPrefix greedyDeletedPrimeClass X).card =
      primeCutoffLength X - (primeClassPrefix greedyPrimeClass X).card := by
  rw [primeClassPrefix_card_eq_selectionCount, classPrimeIndices_greedyDeletedPrimeClass,
    selectionCount_not_eq_sub, greedyPrimeClass_count_eq]

theorem greedyDeletedPrimeClass_count_optimal
    (P : Set Nat) (hP : forall X : Nat, primeClassTheta P X <= (X : Real)) (X : Nat) :
    (primeClassPrefix greedyDeletedPrimeClass X).card <=
      (primeClassPrefix (fun p => Not (Membership.mem P p)) X).card := by
  rw [greedyDeletedPrimeClass_count_eq_sub, primeClassPrefix_complement_card]
  exact Nat.sub_le_sub_left (greedyPrimeClass_count_optimal P hP X) (primeCutoffLength X)

end PrimeFactorOscillations.PrimeClassDeletion
