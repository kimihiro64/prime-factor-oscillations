/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A finite weighted drift bound

A bounded positive contribution at each index cannot offset a monotone
endpoint drop when the index count is small relative to its coefficient.
The proof retains both contributions before summing.
-/

namespace Finset

private theorem drift_telescope (u : Nat -> Real) (n : Nat) :
    (range n).sum (fun i => u i - u (i + 1)) = u 0 - u n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    linarith

/-- A monotone drop dominates bounded row contributions in a short sum. -/
theorem sum_range_weighted_drift_le (n : Nat) (P : Real)
    (u w v : Nat -> Real)
    (hP : 0 <= P) (hn : (n : Real) <= P / 256)
    (hu : forall i, i <= n -> 0 <= u i /\ u i <= 1)
    (hmono : forall i, i < n -> u (i + 1) <= u i)
    (hw : forall i, i < n -> 1 / 3 <= w i /\ w i <= 2)
    (hv : forall i, i < n -> v i <= 3)
    (hdrop : 1 / 6 <= u 0 - u n) :
    (range n).sum (fun i =>
      w i * ((v i - 1) * u i * u (i + 1) -
        P / 2 * (u i - u (i + 1)))) <= -7 * P / 576 := by
  have hterm : forall i, Membership.mem (range n) i ->
      w i * ((v i - 1) * u i * u (i + 1) -
        P / 2 * (u i - u (i + 1))) <=
          4 - P / 6 * (u i - u (i + 1)) := by
    intro i hi
    have hin : i < n := mem_range.mp hi
    have hi0 := hu i (Nat.le_of_lt hin)
    have hi1 := hu (i + 1) (Nat.succ_le_of_lt hin)
    have hwi := hw i hin
    have hw0 : 0 <= w i := by linarith
    have hprod0 : 0 <= u i * u (i + 1) :=
      mul_nonneg hi0.1 hi1.1
    have hprod1 : u i * u (i + 1) <= 1 := by
      calc
        _ <= 1 * u (i + 1) :=
          mul_le_mul_of_nonneg_right hi0.2 hi1.1
        _ <= 1 := by simpa only [one_mul] using hi1.2
    have hvv : (v i - 1) * (u i * u (i + 1)) <= 2 := by
      have hh := mul_le_mul_of_nonneg_right
        (show v i - 1 <= 2 by linarith [hv i hin]) hprod0
      nlinarith
    have hsupply : w i * ((v i - 1) * (u i * u (i + 1))) <= 4 := by
      have hh := mul_le_mul_of_nonneg_left hvv hw0
      nlinarith
    have hdiff : 0 <= u i - u (i + 1) := sub_nonneg.mpr (hmono i hin)
    have hcost : 0 <= P / 2 * (u i - u (i + 1)) :=
      mul_nonneg (by linarith) hdiff
    have hloss := mul_le_mul_of_nonneg_right hwi.1 hcost
    nlinarith
  calc
    _ <= (range n).sum (fun i => 4 - P / 6 * (u i - u (i + 1))) :=
      sum_le_sum hterm
    _ = 4 * (n : Real) - P / 6 * (u 0 - u n) := by
      rw [sum_sub_distrib, <- mul_sum, drift_telescope]
      simp only [sum_const, card_range, nsmul_eq_mul]
      linarith
    _ <= -7 * P / 576 := by
      have hh := mul_le_mul_of_nonneg_left hdrop (show 0 <= P / 6 by linarith)
      nlinarith

end Finset
