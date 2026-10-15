/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDynamics
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.LargestPrimeFactorFrontier

/-!
# Exact weights of actual LPF-generated states

The weights count ordered distinct pairs in the supplied finite state, without
replacing that state by a full prime interval. The frontier count is only a
sufficient condition for growth: missing output primes below the maximum may
also enlarge the state. All pair multiplicities and finite endpoints are exact.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def distinctPairs (S : Finset Nat) : Finset (Prod Nat Nat) :=
  (S.product S).filter (fun a => Not (a.1 = a.2))

def pairWeight (S : Finset Nat) (n : Nat) : Nat :=
  ((distinctPairs S).filter (fun a => affineValue a.1 a.2 = n)).card

def frontierCount (S : Finset Nat) (M : Nat) : Nat :=
  ((distinctPairs S).filter (fun a => M < Nat.largestPrimeFactor (affineValue a.1 a.2))).card

def newFactorCount (S : Finset Nat) : Nat :=
  ((distinctPairs S).filter
    (fun a => Not (Membership.mem S (Nat.largestPrimeFactor (affineValue a.1 a.2))))).card

theorem pairWeight_even (S : Finset Nat) (n : Nat) : pairWeight S (2 * n) = 0 := by
  apply Finset.card_eq_zero.mpr
  ext a
  constructor
  next =>
    intro ha
    exfalso
    have h := Finset.mem_filter.mp ha
    have hne := (Finset.mem_filter.mp h.1).2
    have heq := h.2
    unfold affineValue at heq
    omega
  next =>
    intro ha
    exact False.elim (by simpa using ha)

theorem frontierCount_eq_sum_pairWeight (S : Finset Nat) (M : Nat)
    (hBound : forall p, Membership.mem S p -> p <= M) :
    frontierCount S M = Finset.sum ((Finset.Icc 1 (4 * M - 1)).filter
      (fun n => M < Nat.largestPrimeFactor n)) (pairWeight S) := by
  have hSupport : forall a, Membership.mem (distinctPairs S) a ->
      Membership.mem (Finset.Icc 1 (4 * M - 1)) (affineValue a.1 a.2) := by
    intro a ha
    have hPair := Finset.mem_filter.mp ha
    have hInputs := Finset.mem_product.mp hPair.1
    have hp := hBound a.1 hInputs.1
    have hq := hBound a.2 hInputs.2
    apply Finset.mem_Icc.mpr
    unfold affineValue
    omega
  let T := (Finset.Icc 1 (4 * M - 1)).filter (fun n => M < Nat.largestPrimeFactor n)
  have h := Finset.sum_fiberwise_eq_sum_filter (distinctPairs S) T
    (fun a => affineValue a.1 a.2) (fun _ => (1 : Nat))
  have hFilter : (distinctPairs S).filter (fun a => Membership.mem T (affineValue a.1 a.2)) =
      (distinctPairs S).filter (fun a => M < Nat.largestPrimeFactor (affineValue a.1 a.2)) := by
    apply Finset.filter_congr
    intro a ha
    simp only [T, Finset.mem_filter, hSupport a ha, true_and]
  rw [hFilter] at h
  change ((distinctPairs S).filter (fun a =>
    M < Nat.largestPrimeFactor (affineValue a.1 a.2))).card =
      Finset.sum T (fun n => ((distinctPairs S).filter
        (fun a => affineValue a.1 a.2 = n)).card)
  simpa using h.symm

theorem frontierCount_eq_two_prime_rows (S : Finset Nat) (M : Nat) (hM : 3 <= M)
    (hBound : forall p, Membership.mem S p -> p <= M) :
    frontierCount S M =
      Finset.sum ((Finset.Icc (M + 1) (4 * M - 1)).filter Nat.Prime) (pairWeight S) +
      Finset.sum ((Finset.Icc (M + 1) ((4 * M - 1) / 3)).filter Nat.Prime)
        (fun r => pairWeight S (3 * r)) := by
  rw [frontierCount_eq_sum_pairWeight S M hBound]
  exact Nat.sum_largestPrimeFactor_frontier_eq_two_rows (pairWeight S) (pairWeight_even S) M hM

theorem frontierCount_le_newFactorCount (S : Finset Nat) (M : Nat)
    (hBound : forall p, Membership.mem S p -> p <= M) : frontierCount S M <= newFactorCount S := by
  apply Finset.card_le_card
  intro a ha
  have h := Finset.mem_filter.mp ha
  apply Finset.mem_filter.mpr
  refine And.intro h.1 ?_
  intro hOld
  have hle := hBound _ hOld
  exact (not_lt_of_ge hle) h.2

theorem newFactorCount_eq_zero_iff_closed (S : Finset Nat) :
    newFactorCount S = 0 <-> step S = S := by
  classical
  rw [step_eq_self_iff]
  constructor
  next =>
    intro h p q hp hq hne
    by_contra hMissing
    have hEmpty := Finset.card_eq_zero.mp h
    have hMem : Membership.mem
        ((distinctPairs S).filter (fun a =>
          Not (Membership.mem S (Nat.largestPrimeFactor (affineValue a.1 a.2))))) (p, q) := by
      apply Finset.mem_filter.mpr
      refine And.intro ?_ hMissing
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_product.mpr (And.intro hp hq)) hne)
    rw [hEmpty] at hMem
    simpa using hMem
  next =>
    intro h
    apply Finset.card_eq_zero.mpr
    ext a
    constructor
    next =>
      intro ha
      exfalso
      have hOuter := Finset.mem_filter.mp ha
      have hPair := Finset.mem_filter.mp hOuter.1
      have hInputs := Finset.mem_product.mp hPair.1
      exact hOuter.2 (h a.1 a.2 hInputs.1 hInputs.2 hPair.2)
    next =>
      intro ha
      exact False.elim (by simpa using ha)

theorem not_closed_of_frontierCount_pos (S : Finset Nat) (M : Nat)
    (hBound : forall p, Membership.mem S p -> p <= M) (hPositive : 0 < frontierCount S M) :
    Not (step S = S) := by
  intro hClosed
  have hZero := (newFactorCount_eq_zero_iff_closed S).mpr hClosed
  have hle := frontierCount_le_newFactorCount S M hBound
  omega

end PrimeFactorOscillations.LPF
