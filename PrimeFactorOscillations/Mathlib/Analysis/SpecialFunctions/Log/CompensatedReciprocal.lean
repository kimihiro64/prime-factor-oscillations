/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Compensated reciprocal logarithms

Two-sided signed comparison and cubic decay for a bounded displacement.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace Real

def bernoulliLogProfile (t x : Real) : Real := Real.log (1 + t / x) - t / x

def pairLogDefect (t p q : Real) : Real :=
  bernoulliLogProfile t q - bernoulliLogProfile t p

/-- Exact two-sided signed compensation bounds; no main term is discarded. -/
theorem pairLogDefect_bounds (t p q : Real) (ht : 0 <= t)
    (hp : 0 < p) (hq : 0 < q) :
    t ^ 2 * (q - p) / (p * q * (q + t)) <= pairLogDefect t p q /\
      pairLogDefect t p q <= t ^ 2 * (q - p) / (p * q * (p + t)) := by
  have ha : 0 < 1 + t / p := by positivity
  have hb : 0 < 1 + t / q := by positivity
  have hpt : 0 < p + t := add_pos_of_pos_of_nonneg hp ht
  have hqt : 0 < q + t := add_pos_of_pos_of_nonneg hq ht
  have hu := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hl := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div hb.ne' ha.ne'] at hu
  rw [Real.log_div ha.ne' hb.ne'] at hl
  have hd : pairLogDefect t p q =
      (Real.log (1 + t / q) - Real.log (1 + t / p)) + (t / p - t / q) := by
    unfold pairLogDefect bernoulliLogProfile
    ring
  constructor
  . calc
      _ = (1 - (1 + t / p) / (1 + t / q)) + (t / p - t / q) := by
        field_simp [hp.ne', hq.ne', hpt.ne', hqt.ne']
        <;> ring
      _ <= (Real.log (1 + t / q) - Real.log (1 + t / p)) + (t / p - t / q) := by
        linarith only [hl]
      _ = _ := hd.symm
  . calc
      _ = (Real.log (1 + t / q) - Real.log (1 + t / p)) + (t / p - t / q) := hd
      _ <= ((1 + t / q) / (1 + t / p) - 1) + (t / p - t / q) :=
        _root_.add_le_add hu (le_refl _)
      _ = _ := by
        field_simp [hp.ne', hq.ne', hpt.ne', hqt.ne']
        <;> ring

/-- The complete compensated defect has cubic decay for bounded displacements. -/
theorem pairLogDefect_cubic (t p q : Real) (ht : 0 <= t)
    (hp : 0 < p) (hpq : p <= q) :
    0 <= pairLogDefect t p q /\
      pairLogDefect t p q <= t ^ 2 * (q - p) / p ^ 3 := by
  have hq : 0 < q := hp.trans_le hpq
  have hb := pairLogDefect_bounds t p q ht hp hq
  have hnum : 0 <= t ^ 2 * (q - p) :=
    mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hpq)
  have hden : p ^ 3 <= p * q * (p + t) := by
    have h1 := mul_le_mul_of_nonneg_left hpq (sq_nonneg p)
    have h2 := mul_nonneg (mul_nonneg hp.le hq.le) ht
    nlinarith only [h1, h2]
  exact And.intro ((div_nonneg hnum (by positivity)).trans hb.1)
    (hb.2.trans (div_le_div_of_nonneg_left hnum (pow_pos hp 3) hden))

end Real
