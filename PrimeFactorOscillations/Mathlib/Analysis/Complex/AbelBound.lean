/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# A finite norm bound for decreasing weights

Summation by parts transfers a uniform bound for all initial sums without
discarding the cancellation in those sums.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

theorem norm_sum_range_smul_le_of_antitone
    (a : Nat -> Real) (f : Nat -> Complex) (N : Nat) (M : Real)
    (ha : Antitone a) (ha0 : forall i, 0 <= a i)
    (hprefix : forall n, n <= N -> norm (Finset.sum (Finset.range n) f) <= M) :
    norm (Finset.sum (Finset.range N) (fun i => HSMul.hSMul (a i) (f i))) <= a 0 * M := by
  have hM : 0 <= M := by simpa using hprefix 0 (Nat.zero_le N)
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg (ha0 0) hM
  | succ n =>
    have hlast : norm (HSMul.hSMul (a n) (Finset.sum (Finset.range (n + 1)) f)) <= a n * M := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
      exact mul_le_mul_of_nonneg_left (hprefix (n + 1) le_rfl) (ha0 n)
    have hterm : forall i, Membership.mem (Finset.range n) i ->
        norm (HSMul.hSMul (a (i + 1) - a i) (Finset.sum (Finset.range (i + 1)) f)) <=
          (a i - a (i + 1)) * M := by
      intro i hi
      have hdiff : a (i + 1) <= a i := ha (Nat.le_succ i)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hdiff), neg_sub]
      exact mul_le_mul_of_nonneg_left
        (hprefix (i + 1) ((Nat.succ_le_of_lt (Finset.mem_range.mp hi)).trans (Nat.le_succ n)))
        (sub_nonneg.mpr hdiff)
    have htel : Finset.sum (Finset.range n) (fun i => a i - a (i + 1)) = a 0 - a n := by
      calc
        _ = -(Finset.sum (Finset.range n) (fun i => a (i + 1) - a i)) := by
          calc
            _ = Finset.sum (Finset.range n) (fun i => -(a (i + 1) - a i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = _ := by simp only [Finset.sum_neg_distrib]
        _ = _ := by rw [Finset.sum_range_sub]; ring
    rw [Finset.sum_range_by_parts]
    simp only [Nat.add_sub_cancel]
    calc
      _ <= norm (HSMul.hSMul (a n) (Finset.sum (Finset.range (n + 1)) f)) +
          norm (Finset.sum (Finset.range n)
            (fun i => HSMul.hSMul (a (i + 1) - a i) (Finset.sum (Finset.range (i + 1)) f))) :=
        norm_sub_le _ _
      _ <= a n * M + Finset.sum (Finset.range n) (fun i => (a i - a (i + 1)) * M) :=
        add_le_add hlast ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
      _ = a 0 * M := by
        rw [(Finset.sum_mul (Finset.range n) (fun i => a i - a (i + 1)) M).symm, htel]
        ring

theorem norm_sum_range_smul_le_of_monotone
    (a : Nat -> Real) (f : Nat -> Complex) (N : Nat) (M W : Real)
    (ha : Monotone a) (ha0 : 0 <= a 0) (hM : 0 <= M) (hW : 0 <= W)
    (haW : forall i, i < N -> a i <= W)
    (hprefix : forall n, n <= N -> norm (Finset.sum (Finset.range n) f) <= M) :
    norm (Finset.sum (Finset.range N) (fun i => HSMul.hSMul (a i) (f i))) <= 2 * W * M := by
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  | succ n =>
    have hn : 0 <= a n := ha0.trans (ha (Nat.zero_le n))
    have hlast : norm (HSMul.hSMul (a n) (Finset.sum (Finset.range (n + 1)) f)) <= a n * M := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
      exact mul_le_mul_of_nonneg_left (hprefix (n + 1) le_rfl) hn
    have hterm : forall i, Membership.mem (Finset.range n) i ->
        norm (HSMul.hSMul (a (i + 1) - a i) (Finset.sum (Finset.range (i + 1)) f)) <=
          (a (i + 1) - a i) * M := by
      intro i hi
      have hdiff : 0 <= a (i + 1) - a i := sub_nonneg.mpr (ha (Nat.le_succ i))
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
      exact mul_le_mul_of_nonneg_left
        (hprefix (i + 1) ((Nat.succ_le_of_lt (Finset.mem_range.mp hi)).trans (Nat.le_succ n))) hdiff
    rw [Finset.sum_range_by_parts]
    simp only [Nat.add_sub_cancel]
    calc
      _ <= norm (HSMul.hSMul (a n) (Finset.sum (Finset.range (n + 1)) f)) +
          norm (Finset.sum (Finset.range n)
            (fun i => HSMul.hSMul (a (i + 1) - a i) (Finset.sum (Finset.range (i + 1)) f))) := norm_sub_le _ _
      _ <= a n * M + Finset.sum (Finset.range n) (fun i => (a (i + 1) - a i) * M) :=
        add_le_add hlast ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
      _ = (2 * a n - a 0) * M := by
        rw [<- Finset.sum_mul, Finset.sum_range_sub]
        ring
      _ <= 2 * W * M := by
        have h := haW n (Nat.lt_succ_self n)
        nlinarith only [h, ha0, hM]


end Finset
