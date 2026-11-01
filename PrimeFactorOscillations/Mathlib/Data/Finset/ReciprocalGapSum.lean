/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A reciprocal gap sum with one excluded integer

The elementary telescope over all integers at least two has mass at most
one. Excluding four leaves a uniform allowance of eleven twelfths. The
finite support is arbitrary; primality is not assumed or needed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

/-- A finite reciprocal telescope with the contribution at four removed. -/
theorem sum_inv_mul_pred_le_of_four_notMem
    (S : Finset Nat)
    (hmin : forall n : Nat, Membership.mem S n -> 2 <= n)
    (hfour : Not (Membership.mem S 4)) :
    Finset.sum S (fun n => 1 / ((n : Real) * ((n : Real) - 1))) <= 11 / 12 := by
  let f : Nat -> Real := fun n => 1 / ((n : Real) * ((n : Real) - 1))
  change Finset.sum S f <= 11 / 12
  have htelescope : forall n : Nat,
      Finset.sum (Finset.Ico 2 (n + 2)) f = 1 - 1 / ((n : Real) + 1) := by
    intro n
    induction n with
    | zero => norm_num [f]
    | succ n ih =>
      rw [Finset.sum_Ico_succ_top (by omega : 2 <= n + 2), ih]
      simp only [Nat.cast_succ]
      have hn : 0 <= (n : Real) := Nat.cast_nonneg n
      have he2 : (n : Real) + 1 + 1 = (n : Real) + 2 := by ring
      rw [he2]
      have he : (n : Real) + 2 - 1 = (n : Real) + 1 := by ring
      rw [he]
      have h1 : Not ((n : Real) + 1 = 0) := by linarith
      have h2 : Not ((n : Real) + 2 = 0) := by linarith
      field_simp
      ring
  let N := Finset.sum S (fun n => n) + 4
  have hN : 4 <= N := by dsimp [N]; omega
  have hbound (n : Nat) (hn : Membership.mem S n) : n <= N := by
    have hsum : n <= Finset.sum S (fun k => k) :=
      Finset.single_le_sum (fun k _ => Nat.zero_le k) hn
    dsimp [N]
    omega
  have hsub : forall n : Nat, Membership.mem (insert 4 S) n ->
      Membership.mem (Finset.Ico 2 (N + 2)) n := by
    intro n hn
    rcases Finset.mem_insert.mp hn with he | hs
    . subst n
      exact Finset.mem_Ico.mpr (And.intro (by omega) (by omega))
    . exact Finset.mem_Ico.mpr (And.intro (hmin n hs) (by have hb := hbound n hs; omega))
  have hnonneg (n : Nat) (hn : 2 <= n) : 0 <= f n := by
    have hn2 : (2 : Real) <= n := by exact_mod_cast hn
    dsimp only [f]
    exact div_nonneg (by norm_num)
      (mul_nonneg (Nat.cast_nonneg n) (by linarith))
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n hn _ => hnonneg n (Finset.mem_Ico.mp hn).1)
  rw [Finset.sum_insert hfour] at hsum
  have hf4 : f 4 = 1 / 12 := by norm_num [f]
  rw [hf4, htelescope N] at hsum
  have hrecip : 0 <= 1 / ((N : Real) + 1) :=
    div_nonneg (by norm_num) (add_nonneg (Nat.cast_nonneg N) (by norm_num))
  linarith

end Finset
