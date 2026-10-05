/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Marker aggregation and powerset moments

A difference of two nonnegative marker totals is bounded by one marker
count. Squared coefficients bounded by cardinality times a subset power
are controlled by the fifth powerset moment. The cross-multiplied tail
bound retains the empty subset and is valid without dividing by a cutoff.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

variable {iota : Type*}

/-- Two nonnegative marker totals share one bound, so their difference does too. -/
theorem abs_sum_sub_sum_le_card_mul_marker (s : Finset iota)
    (a b : iota -> Real) (B : Real)
    (ha : forall i, Membership.mem s i -> 0 <= a i)
    (hb : forall i, Membership.mem s i -> 0 <= b i)
    (haB : forall i, Membership.mem s i -> a i <= B)
    (hbB : forall i, Membership.mem s i -> b i <= B) :
    |s.sum a - s.sum b| <= (s.card : Real) * B := by
  have ha0 : 0 <= s.sum a := sum_nonneg ha
  have hb0 : 0 <= s.sum b := sum_nonneg hb
  have hau : s.sum a <= (s.card : Real) * B := by
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum haB
  have hbu : s.sum b <= (s.card : Real) * B := by
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hbB
  exact abs_le.mpr (And.intro (by linarith) (by linarith))

/-- A cardinality-weighted powerset moment is controlled by the full cardinality. -/
theorem sum_powerset_card_sq_mul_pow_le (s : Finset iota) (a : Real)
    (ha : 0 <= a) :
    s.powerset.sum (fun t => (t.card : Real) ^ 2 * a ^ t.card) <=
      (s.card : Real) ^ 2 * (a + 1) ^ s.card := by
  classical
  have hsum : s.powerset.sum (fun t => a ^ t.card) = (a + 1) ^ s.card := by
    have hp := prod_add (fun _ : iota => a) (fun _ : iota => (1 : Real)) s
    simpa only [prod_const, one_pow, mul_one] using hp.symm
  calc
    _ <= s.powerset.sum (fun t => (s.card : Real) ^ 2 * a ^ t.card) := by
      apply sum_le_sum
      intro t ht
      have hcard : (t.card : Real) <= s.card := by
        exact_mod_cast card_le_card (mem_powerset.mp ht)
      have hsq : (t.card : Real) ^ 2 <= (s.card : Real) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self (Nat.cast_nonneg t.card) hcard
      exact mul_le_mul_of_nonneg_right hsq (pow_nonneg ha _)
    _ = _ := by rw [<- mul_sum, hsum]

/-- Summing squared marker coefficients costs a fifth divisor moment. -/
theorem sum_powerset_sq_le_five_pow_of_marker_bound (s : Finset iota)
    (c : Finset iota -> Real)
    (hc : forall t, Membership.mem s.powerset t ->
      |c t| <= (t.card : Real) * 2 ^ t.card) :
    s.powerset.sum (fun t => c t ^ 2) <= (s.card : Real) ^ 2 * 5 ^ s.card := by
  have htwo (t : Finset iota) : ((2 : Real) ^ t.card) ^ 2 = 4 ^ t.card := by
    rw [<- pow_mul, Nat.mul_comm t.card 2, pow_mul]
    norm_num
  calc
    _ <= s.powerset.sum (fun t => (t.card : Real) ^ 2 * 4 ^ t.card) := by
      apply sum_le_sum
      intro t ht
      have hh : |c t| ^ 2 <= ((t.card : Real) * 2 ^ t.card) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self (abs_nonneg (c t)) (hc t ht)
      simpa only [sq_abs, mul_pow, htwo] using hh
    _ <= _ := by
      simpa only [show (4 : Real) + 1 = 5 by norm_num] using
        sum_powerset_card_sq_mul_pow_le s 4 (by norm_num)

/-- Cross-multiplied tail bound; division by H is valid when H is positive. -/
theorem mul_sum_powerset_abs_tail_le_marker_moment (s : Finset iota)
    (c : Finset iota -> Real) (H : Real)
    (hc : forall t, Membership.mem s.powerset t ->
      |c t| <= (t.card : Real) * 2 ^ t.card) :
    H * s.powerset.sum (fun t => if H < |c t| then |c t| else 0) <=
      (s.card : Real) ^ 2 * 5 ^ s.card := by
  calc
    _ <= s.powerset.sum (fun t => c t ^ 2) := by
      rw [mul_sum]
      apply sum_le_sum
      intro t ht
      by_cases hh : H < |c t|
      case pos =>
        simp only [hh, ite_true]
        have hm := mul_le_mul_of_nonneg_right (le_of_lt hh) (abs_nonneg (c t))
        simpa only [<- pow_two, sq_abs] using hm
      case neg =>
        simp only [hh, ite_false, mul_zero]
        exact sq_nonneg (c t)
    _ <= _ := sum_powerset_sq_le_five_pow_of_marker_bound s c hc

end Finset
