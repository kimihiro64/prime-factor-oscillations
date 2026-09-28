/-
Copyright (c) 2026 Prime Factor Oscillations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Uniform finite inverse-square budget -/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

/-- Telescoping gives a uniform finite inverse-square budget, including the
empty range. The explicit remainder is retained in the induction. -/
theorem sum_range_inverse_square_le (n : Nat) :
    (Finset.range n).sum (fun i => 1 / ((i : Real) + 1) ^ 2) <=
      2 - 2 / ((n : Real) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hn : (0 : Real) <= n := Nat.cast_nonneg n
      have ht : 0 < (n : Real) + 1 := by linarith
      have hu : 0 < (n : Real) + 2 := by linarith
      have hstep : 1 / ((n : Real) + 1) ^ 2 <=
          2 / ((n : Real) + 1) - 2 / ((n : Real) + 2) := by
        have hc : (1 / ((n : Real) + 1) ^ 2 -
            (2 / ((n : Real) + 1) - 2 / ((n : Real) + 2))) *
            (((n : Real) + 1) ^ 2 * ((n : Real) + 2)) = -(n : Real) := by
          field_simp
          ring
        have hd : 0 < ((n : Real) + 1) ^ 2 * ((n : Real) + 2) :=
          mul_pos (sq_pos_of_pos ht) hu
        nlinarith only [hc, hd, hn]
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show (n : Real) + 1 + 1 = n + 2 by ring]
      linarith only [ih, hstep]

/-- The uniform budget also applies to the unshifted range, since its zero
term contributes zero under field division. -/
theorem sum_range_unshifted_inverse_square_le (n : Nat) :
    (Finset.range n).sum (fun i => 1 / (i : Real) ^ 2) <= 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero,
        zero_pow (by norm_num : Not ((2 : Nat) = 0)),
        div_zero, add_zero]
      have h := sum_range_inverse_square_le n
      have hn : (0 : Real) <= n := Nat.cast_nonneg n
      have hd : 0 <= 2 / ((n : Real) + 1) := div_nonneg (by norm_num) (by linarith)
      linarith only [h, hd]

/-- Restriction to any subset preserves the same absolute budget. -/
theorem sum_subset_inverse_square_le (E : Finset Nat) (N : Nat)
    (hE : forall p, Membership.mem E p -> Membership.mem (Finset.range N) p) :
    E.sum (fun i => 1 / (i : Real) ^ 2) <= 2 := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg hE
    (fun (i : Nat) _ _ => div_nonneg (by norm_num : (0 : Real) <= 1) (sq_nonneg (i : Real)))
  exact h.trans (sum_range_unshifted_inverse_square_le N)

/-- Every signed perturbation with an inverse-square majorant has uniformly
bounded total error on every finite subset of the natural range. -/
theorem abs_sum_le_inverse_square_budget (E : Finset Nat) (N : Nat)
    (hE : forall p, Membership.mem E p -> Membership.mem (Finset.range N) p)
    (f : Nat -> Real) (D : Real) (hD : 0 <= D)
    (hf : forall p, Membership.mem E p -> abs (f p) <= D / (p : Real) ^ 2) :
    abs (E.sum f) <= 2 * D := by
  calc
    abs (E.sum f) <= E.sum (fun p => abs (f p)) := Finset.abs_sum_le_sum_abs _ _
    _ <= E.sum (fun p => D / (p : Real) ^ 2) := Finset.sum_le_sum hf
    _ = D * E.sum (fun p => 1 / (p : Real) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ <= D * 2 := mul_le_mul_of_nonneg_left (sum_subset_inverse_square_le E N hE) hD
    _ = 2 * D := mul_comm _ _

end Finset
