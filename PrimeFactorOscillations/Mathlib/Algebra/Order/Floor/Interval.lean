/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# A moving floor rank on a nearby positive interval

A one-unit perturbation of a sufficiently large clock keeps the floored rank
positive and its quotient in an explicit fixed compact interval.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem floor_mul_div_mem_compact_of_abs_sub_le_one
    (alpha B L : Real) (ha : 0 < alpha) (hL : 2 <= L)
    (haL : 2 <= alpha * L) (hBL : abs (B - L) <= 1) :
    0 < Nat.floor (alpha * L) /\
      forall u : Real, Set.Icc (min B L) (max B L) u ->
        0 < u /\ alpha / 3 <= (Nat.floor (alpha * L) : Real) / u /\
          (Nat.floor (alpha * L) : Real) / u <= 2 * alpha := by
  have hLpos : 0 < L := by linarith
  have haL0 : 0 <= alpha * L := (_root_.mul_pos ha hLpos).le
  have hfloorHi := Nat.floor_le haL0
  have hfloorLo := Nat.lt_floor_add_one (alpha * L)
  have hfloorHalf : alpha * L / 2 <= (Nat.floor (alpha * L) : Real) := by linarith
  have hfloorPos : 0 < Nat.floor (alpha * L) := by
    have hpos : (0 : Real) < Nat.floor (alpha * L) := by linarith
    exact_mod_cast hpos
  refine And.intro hfloorPos ?_
  intro u hu
  have hdiff := abs_le.mp hBL
  have hmin : L - 1 <= min B L := _root_.le_min (by linarith) (by linarith)
  have hmax : max B L <= L + 1 := _root_.max_le (by linarith) (by linarith)
  have huLo : L / 2 <= u := by linarith [hmin.trans hu.1]
  have huHi : u <= 3 * L / 2 := by linarith [hu.2.trans hmax]
  have hupos : 0 < u := by linarith
  have hcancel : (Nat.floor (alpha * L) : Real) / u * u = Nat.floor (alpha * L) := by
    field_simp
  have hlo : alpha / 3 <= (Nat.floor (alpha * L) : Real) / u := by
    apply _root_.le_of_mul_le_mul_right _ hupos
    rw [hcancel]
    have hm := _root_.mul_le_mul_of_nonneg_left huHi ha.le
    nlinarith
  have hhi : (Nat.floor (alpha * L) : Real) / u <= 2 * alpha := by
    apply _root_.le_of_mul_le_mul_right _ hupos
    rw [hcancel]
    have hm := _root_.mul_le_mul_of_nonneg_left huLo ha.le
    nlinarith
  exact And.intro hupos (And.intro hlo hhi)

end Nat

