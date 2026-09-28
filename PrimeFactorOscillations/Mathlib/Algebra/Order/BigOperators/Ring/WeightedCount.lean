/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Counting from a weighted excess

A signed weighted sum is bounded by the number of indices whose integer
count is at least two, times the largest possible positive contribution.
No sign is discarded before the complement has been shown nonpositive.
-/

namespace Finset

/-- Bound a weighted excess by the cardinality of its positive support. -/
theorem weighted_excess_le_card_filter {iota : Type*} (s : Finset iota)
    (count : iota -> Nat) (weight : iota -> Real) (J : Nat) (W : Real)
    (hw : forall i, Membership.mem s i -> 0 <= weight i)
    (hW : forall i, Membership.mem s i -> weight i <= W)
    (hc : forall i, Membership.mem s i -> count i <= J) :
    s.sum (fun i => ((count i : Real) - 1) * weight i) <=
      ((s.filter (fun i => 2 <= count i)).card : Real) * (((J : Real) - 1) * W) := by
  classical
  have hterm : forall i, Membership.mem s i ->
      ((count i : Real) - 1) * weight i <=
        if 2 <= count i then ((J : Real) - 1) * W else 0 := by
    intro i hi
    by_cases hp : 2 <= count i
    case pos =>
      rw [ite_eq_left hp]
      have hcR : (count i : Real) <= J := by exact_mod_cast hc i hi
      have hpR : (2 : Real) <= count i := by exact_mod_cast hp
      exact mul_le_mul (by linarith) (hW i hi) (hw i hi) (by linarith)
    case neg =>
      rw [ite_eq_right hp]
      have hc1 : count i <= 1 := by omega
      have hcR : (count i : Real) <= 1 := by exact_mod_cast hc1
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hw i hi)
  calc
    _ <= s.sum (fun i => if 2 <= count i then ((J : Real) - 1) * W else 0) :=
      Finset.sum_le_sum hterm
    _ = _ := by rw [<- Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- The corresponding bound stated as the difference of two moments. -/
theorem weighted_moments_sub_le_card_filter {iota : Type*} (s : Finset iota)
    (count : iota -> Nat) (weight : iota -> Real) (J : Nat) (W : Real)
    (hw : forall i, Membership.mem s i -> 0 <= weight i)
    (hW : forall i, Membership.mem s i -> weight i <= W)
    (hc : forall i, Membership.mem s i -> count i <= J) :
    s.sum (fun i => (count i : Real) * weight i) - s.sum weight <=
      ((s.filter (fun i => 2 <= count i)).card : Real) * (((J : Real) - 1) * W) := by
  simpa only [sub_mul, one_mul, Finset.sum_sub_distrib] using
    weighted_excess_le_card_filter s count weight J W hw hW hc

end Finset
