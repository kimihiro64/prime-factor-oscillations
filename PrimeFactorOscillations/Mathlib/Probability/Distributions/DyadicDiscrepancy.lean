/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A signed binary discrepancy bound

The inverse binary branches x/2 and (x+1)/2 admit a common
piecewise-linear compensator. Telescoping it bounds the full retained
binary reward by k/3+1, rather than bounding every digit separately.
For a positive sample size N this is the arithmetic core of the
total-variation bound k/(6*N)+1/(2*N).
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace DyadicDiscrepancy

def step (b : Bool) (x : Real) : Real :=
  (x + if b then 1 else 0) / 2

def reward (b : Bool) (x : Real) : Real :=
  if b then 1 - x else 0

def balance (x : Real) : Real :=
  x - abs (x - 1 / 2) / 3

theorem balance_zero : balance 0 = -(1 / 6 : Real) := by
  norm_num [balance]

theorem balance_le {x : Real} (hx : x <= 1) : balance x <= 5 / 6 := by
  have h := le_abs_self (x - 1 / 2)
  unfold balance
  linarith

theorem step_mem_unit (b : Bool) {x : Real} (h0 : 0 <= x) (h1 : x <= 1) :
    And (0 <= step b x) (step b x <= 1) := by
  cases b
  next =>
    change And (0 <= (x + 0) / 2) ((x + 0) / 2 <= 1)
    constructor <;> linarith
  next =>
    change And (0 <= (x + 1) / 2) ((x + 1) / 2 <= 1)
    constructor <;> linarith

/-- The exact digit reward is bounded before summing by one common
compensator difference; no independent digit magnitudes are substituted. -/
theorem reward_le_balance_step (b : Bool) {x : Real}
    (h0 : 0 <= x) (h1 : x <= 1) :
    reward b x <= 1 / 3 + balance (step b x) - balance x := by
  cases b with
  | false =>
    change (0 : Real) <= 1 / 3 +
      ((x + 0) / 2 - abs ((x + 0) / 2 - 1 / 2) / 3) -
      (x - abs (x - 1 / 2) / 3)
    simp only [add_zero]
    have hy : x / 2 - 1 / 2 <= 0 := by linarith
    rw [abs_of_nonpos hy]
    by_cases hx : 0 <= x - 1 / 2
    next =>
      rw [abs_of_nonneg hx]
      linarith
    next =>
      rw [abs_of_nonpos (le_of_not_ge hx)]
      linarith
  | true =>
    change 1 - x <= 1 / 3 +
      ((x + 1) / 2 - abs ((x + 1) / 2 - 1 / 2) / 3) -
      (x - abs (x - 1 / 2) / 3)
    have hy : 0 <= (x + 1) / 2 - 1 / 2 := by linarith
    rw [abs_of_nonneg hy]
    by_cases hx : 0 <= x - 1 / 2
    next =>
      rw [abs_of_nonneg hx]
      linarith
    next =>
      rw [abs_of_nonpos (le_of_not_ge hx)]
      linarith

theorem orbit_mem_unit (b : Nat -> Bool) (r : Nat -> Real)
    (h0 : r 0 = 0) (hs : forall t, r (t + 1) = step (b t) (r t))
    (t : Nat) : And (0 <= r t) (r t <= 1) := by
  induction t with
  | zero => rw [h0]; constructor <;> norm_num
  | succ t ih => rw [hs]; exact step_mem_unit (b t) ih.1 ih.2

theorem sum_reward_le_balance (b : Nat -> Bool) (r : Nat -> Real)
    (hr : forall t, And (0 <= r t) (r t <= 1))
    (hs : forall t, r (t + 1) = step (b t) (r t)) (k : Nat) :
    (Finset.sum (Finset.range k) fun t => reward (b t) (r t)) <=
      (k : Real) / 3 + balance (r k) - balance (r 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    have h := reward_le_balance_step (b k) (hr k).1 (hr k).2
    rw [<- hs k] at h
    linarith

theorem sum_reward_le (b : Nat -> Bool) (r : Nat -> Real)
    (h0 : r 0 = 0) (hs : forall t, r (t + 1) = step (b t) (r t))
    (k : Nat) :
    (Finset.sum (Finset.range k) fun t => reward (b t) (r t)) <=
      (k : Real) / 3 + 1 := by
  have hr := orbit_mem_unit b r h0 hs
  have h := sum_reward_le_balance b r hr hs k
  have htop := balance_le (hr k).2
  rw [h0, balance_zero] at h
  linarith

theorem normalized_reward_le (b : Nat -> Bool) (r : Nat -> Real)
    (h0 : r 0 = 0) (hs : forall t, r (t + 1) = step (b t) (r t))
    (k : Nat) {N : Real} (hN : 0 < N) :
    (Finset.sum (Finset.range k) fun t => reward (b t) (r t)) / (2 * N) <=
      (k : Real) / (6 * N) + 1 / (2 * N) := by
  have h := sum_reward_le b r h0 hs k
  have hd : 0 < 2 * N := by linarith
  calc
    _ <= ((k : Real) / 3 + 1) / (2 * N) :=
      div_le_div_of_nonneg_right h (le_of_lt hd)
    _ = (k : Real) / (6 * N) + 1 / (2 * N) := by
      field_simp [ne_of_gt hN]
      ring

/-- The alternating binary orbit has average reward tending to one third. -/
theorem alternating_reward_sum (m : Nat) :
    (Finset.sum (Finset.range m) fun i =>
      1 - (1 - (1 / 4 : Real) ^ i) / 3) =
      2 * (m : Real) / 3 + (4 / 9 : Real) * (1 - (1 / 4 : Real) ^ m) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

end DyadicDiscrepancy
