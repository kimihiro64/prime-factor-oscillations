/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Analysis.Complex.AbelBound

/-!
# Removing logarithmic weights from prime prefixes

A bound for all logarithmically weighted prefixes up to X gives the same
unweighted bound divided by log(2). The proof keeps the partial-sum
cancellation and handles the zero and one endpoints explicitly.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem norm_sum_primesBelow_le_of_weighted_prefix
    (f : Nat -> Complex) (X : Nat) (M : Real)
    (hprefix : forall t, t <= X ->
      norm (Finset.sum (Finset.Icc 1 t)
        (fun n => if Nat.Prime n then HSMul.hSMul (Real.log (n : Real)) (f n) else 0)) <= M) :
    norm (Finset.sum (Nat.primesBelow (X + 1)) f) <= M / Real.log (2 : Real) := by
  let a : Nat -> Real := fun n => 1 / Real.log ((max 2 n : Nat) : Real)
  let g : Nat -> Complex := fun n =>
    if Nat.Prime n then HSMul.hSMul (Real.log (n : Real)) (f n) else 0
  have hPos (n : Nat) : 0 < Real.log ((max 2 n : Nat) : Real) := by
    apply Real.log_pos
    have hTwo : (2 : Real) <= ((max 2 n : Nat) : Real) := by
      exact_mod_cast (le_max_left 2 n)
    linarith
  have ha : Antitone a := by
    intro n m hnm
    apply one_div_le_one_div_of_le (hPos n)
    apply Real.log_le_log
    next =>
      have hTwo : (2 : Real) <= ((max 2 n : Nat) : Real) := by
        exact_mod_cast (le_max_left 2 n)
      linarith
    next => exact_mod_cast max_le_max_left 2 hnm
  have ha0 : forall n, 0 <= a n := fun n => one_div_nonneg.mpr (hPos n).le
  have hM : 0 <= M := by simpa using hprefix 0 (Nat.zero_le X)
  have hRange (m : Nat) : Finset.sum (Finset.range (m + 1)) g =
      Finset.sum (Finset.Icc 1 m) g := by
    have h := Finset.sum_Ico_eq_sub g (Nat.succ_le_succ (Nat.zero_le m))
    have hset : Finset.Ico 1 (m + 1) = Finset.Icc 1 m := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hset] at h
    simpa [g] using h.symm
  have hG : forall n, n <= X + 1 -> norm (Finset.sum (Finset.range n) g) <= M := by
    intro n hn
    cases n with
    | zero => simpa using hM
    | succ m =>
      rw [hRange]
      exact hprefix m (by omega)
  have hIdentity : Finset.sum (Finset.range (X + 1)) (fun n => HSMul.hSMul (a n) (g n)) =
      Finset.sum (Nat.primesBelow (X + 1)) f := by
    unfold Nat.primesBelow
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : Nat.Prime n
    next =>
      have hlog : Not (Real.log (n : Real) = 0) := (Real.log_pos (by
        exact_mod_cast hp.one_lt)).ne'
      simp only [a, g, hp, if_pos, max_eq_right hp.two_le, smul_smul,
        one_div_mul_cancel hlog, one_smul]
    next => simp [g, hp]
  have h := Finset.norm_sum_range_smul_le_of_antitone a g (X + 1) M ha ha0 hG
  rw [hIdentity] at h
  calc
    _ <= a 0 * M := h
    _ = M / Real.log (2 : Real) := by
      norm_num only [a, max_eq_left (Nat.zero_le 2), Nat.cast_ofNat]
      ring

end Nat
