/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-!
Positive local maxima of a sequence with arbitrarily late values of both signs.
This finite-order lemma supplies peak locations, not an analytic oscillation input.
-/

set_option autoImplicit false

universe u

namespace Nat

/-- Bracketing a positive value by negative values gives a positive maximum
whose two adjacent values are no larger. The shifted center avoids predecessors
in applications on unit intervals. -/
theorem exists_ge_pos_adjacent_max_of_unbounded_signs
    {alpha : Type u} [LinearOrder alpha] [Zero alpha] (g : Nat -> alpha)
    (hpos : forall N : Nat, exists n : Nat, N <= n /\ 0 < g n)
    (hneg : forall N : Nat, exists n : Nat, N <= n /\ g n < 0)
    (N : Nat) :
    exists n : Nat, N <= n /\ 2 <= n /\ 0 < g (n + 1) /\
      g n <= g (n + 1) /\ g (n + 2) <= g (n + 1) := by
  classical
  let a := (hneg (N + 3)).choose
  have ha : N + 3 <= a /\ g a < 0 := (hneg (N + 3)).choose_spec
  let b := (hpos (a + 1)).choose
  have hb : a + 1 <= b /\ 0 < g b := (hpos (a + 1)).choose_spec
  let c := (hneg (b + 1)).choose
  have hc : b + 1 <= c /\ g c < 0 := (hneg (b + 1)).choose_spec
  have hbin := Finset.mem_Icc.mpr
    (And.intro (show a <= b by omega) (show b <= c by omega))
  have hnonempty : (Finset.Icc a c).Nonempty := Exists.intro b hbin
  have hmax := Finset.exists_max_image (Finset.Icc a c) g hnonempty
  let x := hmax.choose
  have hx := hmax.choose_spec
  have hbounds : a <= x /\ x <= c := Finset.mem_Icc.mp hx.1
  have hpositive : 0 < g x := _root_.lt_of_lt_of_le hb.2 (hx.2 b hbin)
  have hxa : Not (x = a) := by
    intro heq
    rw [heq] at hpositive
    exact (_root_.lt_asymm hpositive) ha.2
  have hxc : Not (x = c) := by
    intro heq
    rw [heq] at hpositive
    exact (_root_.lt_asymm hpositive) hc.2
  have hleft := Finset.mem_Icc.mpr
    (And.intro (show a <= x - 1 by omega) (show x - 1 <= c by omega))
  have hright := Finset.mem_Icc.mpr
    (And.intro (show a <= x + 1 by omega) (show x + 1 <= c by omega))
  have hcenter : x - 1 + 1 = x := by omega
  have hnext : x - 1 + 2 = x + 1 := by omega
  refine Exists.intro (x - 1) (And.intro (by omega) (And.intro (by omega) ?_))
  rw [hcenter, hnext]
  exact And.intro hpositive (And.intro (hx.2 (x - 1) hleft) (hx.2 (x + 1) hright))

end Nat
