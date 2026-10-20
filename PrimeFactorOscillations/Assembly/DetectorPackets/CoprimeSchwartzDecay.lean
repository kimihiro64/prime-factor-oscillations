/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzSplit

/-!
# CoprimeSchwartzDecay

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

namespace PrimeFactorOscillations.CoprimeSchwartzDecay

open CoprimeSchwartzPoisson CoprimeSchwartzCenter CoprimeSchwartzSplit

theorem global_decay (f : SchwartzMap Real Complex) (k : Nat) :
    exists S : Real, 0 < S /\
      forall x : Real, abs x ^ k * norm (f x) <= S := by
  let S := max 1 ((SchwartzMap.seminorm Real k 0) f)
  refine Exists.intro S (And.intro (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) ?_)
  intro x
  have h := SchwartzMap.le_seminorm Real k 0 f x
  have h' : abs x ^ k * norm (f x) <= (SchwartzMap.seminorm Real k 0) f := by
    simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_zero] using h
  exact h'.trans (le_max_right _ _)

theorem offZero_norm_bound (f : SchwartzMap Real Complex) (k : Nat) (hk : 2 <= k) :
    exists C : Real, 0 < C /\
      forall a : Real, 0 < a -> norm (offZeroSum f a) <= C / a ^ k := by
  choose S hS hdecay using global_decay f k
  let w := fun n : Int => abs (n : Real) ^ (-(k : Real))
  let T := tsum w
  have hkR : (1 : Real) < (k : Real) := by
    exact_mod_cast (show 1 < k from Nat.lt_of_lt_of_le (by decide) hk)
  have hw : Summable w := Real.summable_abs_int_rpow hkR
  have hT : 0 <= T := tsum_nonneg (fun n => Real.rpow_nonneg (abs_nonneg _) _)
  refine Exists.intro (S * (T + 1)) (And.intro (mul_pos hS (by linarith)) ?_)
  intro a ha
  let g := fun n : Int => if n = 0 then 0 else f ((n : Real) * a)
  have hpoint (n : Int) : norm (g n) <= (S / a ^ k) * w n := by
    dsimp only [g, w]
    by_cases hn0 : n = 0
    . rw [if_pos hn0]
      simp only [norm_zero]
      positivity
    . rw [if_neg hn0]
      have hnR : Not ((n : Real) = 0) := Int.cast_ne_zero.mpr hn0
      have hnabs : 0 < abs (n : Real) := abs_pos.mpr hnR
      have hA : 0 < abs (n : Real) ^ k * a ^ k :=
        mul_pos (pow_pos hnabs _) (pow_pos ha _)
      have hd := hdecay ((n : Real) * a)
      rw [abs_mul, abs_of_pos ha, mul_pow] at hd
      rw [Real.rpow_neg (abs_nonneg _) (k : Real), Real.rpow_natCast]
      have hprod : (abs (n : Real) ^ k * a ^ k) *
          ((S / a ^ k) * (abs (n : Real) ^ k) ^ (-1 : Int)) = S := by
        simp only [zpow_neg_one]
        field_simp
      apply le_of_mul_le_mul_left ?_ hA
      rw [show (abs (n : Real) ^ k) ^ (-1 : Int) = (abs (n : Real) ^ k) ^ (-1 : Int) from rfl] at hprod
      simp only [zpow_neg_one] at hprod
      rw [hprod]
      exact hd
  have hmajor : Summable (fun n => (S / a ^ k) * w n) := hw.mul_left _
  have hnorm : Summable (fun n => norm (g n)) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpoint hmajor
  change norm (tsum g) <= _
  calc
    _ <= tsum (fun n => norm (g n)) := norm_tsum_le_tsum_norm hnorm
    _ <= tsum (fun n => (S / a ^ k) * w n) :=
      Summable.tsum_le_tsum hpoint hnorm hmajor
    _ = (S / a ^ k) * T := tsum_mul_left
    _ <= (S / a ^ k) * (T + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end PrimeFactorOscillations.CoprimeSchwartzDecay
