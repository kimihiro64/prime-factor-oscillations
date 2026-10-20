/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.MobiusCompensatedCovariance

/-!
# MobiusSignedDivisorTail

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.MobiusSignedDivisorTail

theorem reciprocal_square_interval (T k : Nat) (hT : 0 < T) :
    (Finset.Ioc T (T + k)).sum (fun d => 1 / (d : Real) ^ 2) <=
      1 / (T : Real) - 1 / ((T + k : Nat) : Real) := by
  induction k with
  | zero => simp
  | succ k ih =>
      let n : Nat := T + k
      have hn : 0 < (n : Real) := by
        dsimp [n]
        exact_mod_cast (show 0 < T + k by omega)
      have hn1 : 0 < (n : Real) + 1 := by linarith
      have hfrac : 1 / (n : Real) - 1 / ((n : Real) + 1) =
          1 / ((n : Real) * ((n : Real) + 1)) := by
        field_simp
        ring
      have hstep : 1 / ((n : Real) + 1) ^ 2 <=
          1 / (n : Real) - 1 / ((n : Real) + 1) := by
        rw [hfrac]
        exact one_div_le_one_div_of_le (mul_pos hn hn1) (by nlinarith)
      have hset : Finset.Ioc T (T + (k + 1)) =
          insert (n + 1) (Finset.Ioc T n) := by
        ext d
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        dsimp [n]
        omega
      have hnot : Not (Membership.mem (Finset.Ioc T n) (n + 1)) := by
        simp only [Finset.mem_Ioc]
        omega
      rw [hset, Finset.sum_insert hnot]
      change 1 / ((n + 1 : Nat) : Real) ^ 2 +
          (Finset.Ioc T n).sum (fun d => 1 / (d : Real) ^ 2) <=
        1 / (T : Real) - 1 / ((n + 1 : Nat) : Real)
      norm_cast at hstep
      change (Finset.Ioc T n).sum (fun d => 1 / (d : Real) ^ 2) <=
        1 / (T : Real) - 1 / (n : Real) at ih
      push_cast
      push_cast at hstep
      linarith

theorem reciprocal_square_tail (T N : Nat) (hT : 0 < T) :
    (Finset.Ioc T N).sum (fun d => 1 / (d : Real) ^ 2) <= 1 / (T : Real) := by
  by_cases hTN : T <= N
  . have h := reciprocal_square_interval T (N - T) hT
    rw [Nat.add_sub_of_le hTN] at h
    exact h.trans (sub_le_self _ (by positivity))
  . have hzero : (Finset.Ioc T N).sum (fun d => 1 / (d : Real) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hb := Finset.mem_Ioc.mp hd
      omega
    rw [hzero]
    positivity

theorem signed_tail_bound (T N : Nat) (hT : 0 < T)
    (A : Real) (hA : 0 <= A) (sign : Nat -> Real) (M : Nat -> Complex)
    (hsign : forall d, Membership.mem (Finset.Ioc T N) d -> abs (sign d) <= 1)
    (hM : forall d, Membership.mem (Finset.Ioc T N) d ->
      norm (M d) <= A / (d : Real)) :
    abs ((Finset.Ioc T N).sum (fun d => sign d * norm (M d) ^ 2)) <=
      A ^ 2 / (T : Real) := by
  calc
    _ <= (Finset.Ioc T N).sum (fun d => abs (sign d * norm (M d) ^ 2)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= (Finset.Ioc T N).sum (fun d => A ^ 2 * (1 / (d : Real) ^ 2)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdR : 0 < (d : Real) := by
        exact_mod_cast (lt_trans hT (Finset.mem_Ioc.mp hd).1)
      have hb := hM d hd
      have hdiv : 0 <= A / (d : Real) := div_nonneg hA hdR.le
      have hsq : norm (M d) ^ 2 <= (A / (d : Real)) ^ 2 := by
        nlinarith [norm_nonneg (M d)]
      rw [abs_mul]
      rw [show abs (norm (M d) ^ 2) = norm (M d) ^ 2 from abs_of_nonneg (sq_nonneg _)]
      calc
        _ <= norm (M d) ^ 2 :=
          (mul_le_mul_of_nonneg_right (hsign d hd) (sq_nonneg _)).trans_eq (one_mul _)
        _ <= (A / (d : Real)) ^ 2 := hsq
        _ = A ^ 2 * (1 / (d : Real) ^ 2) := by ring
    _ = A ^ 2 * (Finset.Ioc T N).sum (fun d => 1 / (d : Real) ^ 2) := by
      rw [Finset.mul_sum]
    _ <= A ^ 2 * (1 / (T : Real)) :=
      mul_le_mul_of_nonneg_left (reciprocal_square_tail T N hT) (sq_nonneg A)
    _ = A ^ 2 / (T : Real) := by ring

end PrimeFactorOscillations.MobiusSignedDivisorTail

