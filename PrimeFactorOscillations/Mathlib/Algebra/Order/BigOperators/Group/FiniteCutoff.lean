/-
Copyright (c) 2026 Prime Factor Oscillations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# Finite-sum allowance from a fixed cutoff

A unit bound below a natural cutoff and a small bound above it control the
sum uniformly over every finite support. This is an elementary counting
inequality; its use does not assume an asymptotic estimate for that support.
-/

set_option autoImplicit false

namespace Finset

/-- A fixed exceptional prefix costs at most its ambient cardinality. -/
theorem sum_le_cutoff_add_card_mul (s : Finset Nat) (f : Nat -> Rat)
    (N : Nat) (c : Rat) (hc : 0 <= c)
    (hsmall : forall p, Membership.mem s p -> p < N -> f p <= 1)
    (hlarge : forall p, Membership.mem s p -> N <= p -> f p <= c) :
    s.sum f <= (N : Rat) + (s.card : Rat) * c := by
  have hcard : (s.filter (fun p => p < N)).card <= N := by
    calc
      _ <= (Finset.range N).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = N := Finset.card_range N
  have hind : s.sum (fun p => if p < N then (1 : Rat) else 0) =
      ((s.filter (fun p => p < N)).card : Rat) := by
    rw [<- Finset.sum_filter]
    simp
  calc
    s.sum f <= s.sum (fun p => (if p < N then (1 : Rat) else 0) + c) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hn : p < N
      next =>
        rw [ite_eq_left hn]
        exact (hsmall p hp hn).trans (le_add_of_nonneg_right hc)
      next =>
        rw [ite_eq_right hn, zero_add]
        exact hlarge p hp (by omega)
    _ = ((s.filter (fun p => p < N)).card : Rat) + (s.card : Rat) * c := by
      rw [Finset.sum_add_distrib, hind]
      simp
    _ <= (N : Rat) + (s.card : Rat) * c := by
      have hcast : ((s.filter (fun p => p < N)).card : Rat) <= (N : Rat) := by
        exact_mod_cast hcard
      linarith

end Finset
