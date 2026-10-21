/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeFactorOscillations.Helpers.PrimeClassSamplingActual
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CapacitySelectionFinite
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

/-!
# Exact transfer between prime indices and literal prime-class cutoffs

The cutoff length counts primes at most X. The image identity retains
both the prime filter and class membership, including cutoffs zero and one.
Consequently recursive selection counts and logarithmic costs are the
actual prime-class cardinalities and theta sums.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

def primeCutoffLength (X : Nat) : Nat := Nat.count Nat.Prime (X + 1)

def classPrimeIndices (P : Set Nat) (i : Nat) : Prop := Membership.mem P (primeAt i)

noncomputable def primeLogWeight (i : Nat) : Real := Real.log (primeAt i : Real)

theorem primeAt_count_prime (p : Nat) (hp : Nat.Prime p) :
    primeAt (Nat.count Nat.Prime p) = p := Nat.nth_count hp

theorem primeCount_primeAt (i : Nat) : Nat.count Nat.Prime (primeAt i) = i :=
  Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime i

theorem primeAt_le_cutoff_iff (i X : Nat) :
    primeAt i <= X <-> i < primeCutoffLength X := by
  constructor
  case mp =>
    intro hi
    have heq : Nat.count Nat.Prime (primeAt i + 1) = i + 1 :=
      Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime i
    have hcount : i + 1 <= Nat.count Nat.Prime (X + 1) := by
      rw [<- heq]
      exact Nat.count_monotone Nat.Prime (Nat.add_le_add_right hi 1)
    exact Nat.lt_of_succ_le hcount
  case mpr =>
    intro hi
    have hlt : Nat.nth Nat.Prime i < X + 1 := Nat.nth_lt_of_lt_count hi
    exact Nat.le_of_lt_succ hlt

theorem primeClassPrefix_eq_indexImage (P : Set Nat) (X : Nat) :
    primeClassPrefix P X =
      (selectionPrefix (classPrimeIndices P) (primeCutoffLength X)).image primeAt := by
  classical
  apply Finset.ext
  intro p
  constructor
  case mp =>
    intro hp
    have hmem := Finset.mem_filter.mp hp
    have hbound := Finset.mem_Icc.mp hmem.1
    let i := Nat.count Nat.Prime p
    have heq : primeAt i = p := primeAt_count_prime p hmem.2.1
    have hi : i < primeCutoffLength X :=
      (primeAt_le_cutoff_iff i X).mp (by rw [heq]; exact hbound.2)
    have hP : classPrimeIndices P i := by
      change Membership.mem P (primeAt i)
      rw [heq]
      exact hmem.2.2
    exact Finset.mem_image.mpr (Exists.intro i (And.intro
      (Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr hi) hP)) heq))
  case mpr =>
    intro hp
    choose i hi using Finset.mem_image.mp hp
    have hmem := Finset.mem_filter.mp hi.1
    have hindex := Finset.mem_range.mp hmem.1
    rw [<- hi.2]
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_Icc.mpr (And.intro (prime_primeAt i).two_le
        ((primeAt_le_cutoff_iff i X).mpr hindex)))
      (And.intro (prime_primeAt i) hmem.2))

theorem primeClassPrefix_card_eq_selectionCount (P : Set Nat) (X : Nat) :
    (primeClassPrefix P X).card = selectionCount (classPrimeIndices P) (primeCutoffLength X) := by
  classical
  calc
    (primeClassPrefix P X).card =
        (selectionPrefix (classPrimeIndices P) (primeCutoffLength X)).card := by
      rw [primeClassPrefix_eq_indexImage,
        Finset.card_image_of_injective _ primeAt_strictMono.injective]
    _ = selectionCount (classPrimeIndices P) (primeCutoffLength X) :=
      (selectionCount_eq_card_selectionPrefix _ _).symm

theorem primeClassPrefix_logSum_eq_selectionCost (P : Set Nat) (X : Nat) :
    (primeClassPrefix P X).sum (fun p => Real.log (p : Real)) =
      selectionCost (classPrimeIndices P) primeLogWeight (primeCutoffLength X) := by
  classical
  calc
    (primeClassPrefix P X).sum (fun p => Real.log (p : Real)) =
        (selectionPrefix (classPrimeIndices P) (primeCutoffLength X)).sum
          (fun i => Real.log (primeAt i : Real)) := by
      rw [primeClassPrefix_eq_indexImage]
      exact Finset.sum_image (fun i _ j _ hij => primeAt_strictMono.injective hij)
    _ = selectionCost (classPrimeIndices P) primeLogWeight (primeCutoffLength X) := by
      rw [selectionCost_eq_sum_selectionPrefix]
      rfl

theorem primeLogWeight_nonneg (i : Nat) : 0 <= primeLogWeight i := by
  apply Real.log_nonneg
  exact_mod_cast (Nat.le_of_lt (one_lt_primeAt i))

theorem primeLogWeight_monotone : Monotone primeLogWeight := by
  intro i j hij
  exact Real.log_le_log (Nat.cast_pos.mpr (prime_primeAt i).pos)
    (Nat.cast_le.mpr (primeAt_strictMono.monotone hij))

end PrimeFactorOscillations.PrimeClassDeletion
