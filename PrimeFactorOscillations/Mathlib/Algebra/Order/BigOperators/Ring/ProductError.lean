/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Quadratic error in a product of complements

For factors in the unit interval, the error after the linear approximation
is nonnegative and bounded by half the square of the sum.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

/-- A second-order bound for a finite product of complements of unit-interval values. -/
theorem prod_one_sub_linear_error_bounds
    {I : Type*} (s : Finset I) (f : I -> Real)
    (hf : forall i, Membership.mem s i -> 0 <= f i /\ f i <= 1) :
    0 <= s.prod (fun i => 1 - f i) - 1 + s.sum f /\
      s.prod (fun i => 1 - f i) - 1 + s.sum f <= (s.sum f) ^ 2 / 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (mem_insert_self a s)
    have hfs : forall i, Membership.mem s i -> 0 <= f i /\ f i <= 1 := by
      intro i hi
      exact hf i (mem_insert_of_mem hi)
    have hs := ih hfs
    have hsum : 0 <= s.sum f := sum_nonneg (fun i hi => (hfs i hi).1)
    rw [prod_insert ha, sum_insert ha]
    constructor
    next =>
      nlinarith [mul_nonneg (sub_nonneg.mpr hfa.2) hs.1,
        mul_nonneg hfa.1 hsum]
    next =>
      nlinarith [mul_nonneg hfa.1 hs.1, sq_nonneg (f a)]

end Finset
