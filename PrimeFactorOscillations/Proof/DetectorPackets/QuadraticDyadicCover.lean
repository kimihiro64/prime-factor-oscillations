/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Basic.Real.Basic

/-!
# QuadraticDyadicCover

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

namespace PrimeFactorOscillations.QuadraticDyadicCover

universe u

theorem dyadic_Ioc_sum {E : Type u} [AddCommMonoid E] (f : Nat -> E) (K : Nat) :
    (Finset.Ioc 1 (2 ^ K)).sum f =
      (Finset.range K).sum (fun k => (Finset.Ioc (2 ^ k) (2 * 2 ^ k)).sum f) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hpos : 0 < 2 ^ K := Nat.pow_pos (by decide)
    have h1 : 1 <= 2 ^ K := hpos
    have h2 : 2 ^ K <= 2 ^ (K + 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_succ K)
    have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by
      rw [pow_succ, Nat.mul_comm]
    calc
      _ = (Finset.Ioc 1 (2 ^ K)).sum f +
          (Finset.Ioc (2 ^ K) (2 ^ (K + 1))).sum f :=
        (Finset.sum_Ioc_consecutive f h1 h2).symm
      _ = _ := by rw [ih, Finset.sum_range_succ, hpow]

theorem dyadic_Icc_sum {E : Type u} [AddCommMonoid E] (f : Nat -> E) (K : Nat) :
    (Finset.Icc 1 (2 ^ K)).sum f =
      f 1 + (Finset.range K).sum
        (fun k => (Finset.Ioc (2 ^ k) (2 * 2 ^ k)).sum f) := by
  have hpos : 1 <= 2 ^ K := Nat.pow_pos (by decide)
  calc
    _ = f 1 + (Finset.Ioc 1 (2 ^ K)).sum f :=
      (Finset.add_sum_Ioc_eq_sum_Icc hpos).symm
    _ = _ := by rw [dyadic_Ioc_sum]

theorem cutoff_power_bound (Z : Nat) (hZ : 0 < Z) :
    2 ^ Z.log2 <= Z /\ Z < 2 ^ (Z.log2 + 1) :=
  (Nat.log2_eq_iff (Nat.ne_of_gt hZ)).mp rfl

theorem band_scale_le_cutoff (Z k : Nat) (hZ : 0 < Z)
    (hk : Membership.mem (Finset.range (Z.log2 + 1)) k) :
    2 ^ k <= Z := by
  have hk1 : k <= Z.log2 := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  exact (Nat.pow_le_pow_right (by decide) hk1).trans (cutoff_power_bound Z hZ).1

theorem cutoff_partition {E : Type u} [AddCommMonoid E] (f : Nat -> E)
    (Z : Nat) (hZ : 0 < Z) :
    (Finset.Icc 1 Z).sum f =
      f 1 + (Finset.range (Z.log2 + 1)).sum (fun k =>
        (Finset.Ioc (2 ^ k) (2 * 2 ^ k)).sum
          (fun d => if d <= Z then f d else 0)) := by
  classical
  have hZpow : Z <= 2 ^ (Z.log2 + 1) := (cutoff_power_bound Z hZ).2.le
  have hFilter :
      (Finset.Icc 1 (2 ^ (Z.log2 + 1))).filter (fun d => d <= Z) =
        Finset.Icc 1 Z := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    . intro h
      exact And.intro h.1.1 h.2
    . intro h
      exact And.intro (And.intro h.1 (h.2.trans hZpow)) h.2
  have hSum := dyadic_Icc_sum (fun d => if d <= Z then f d else 0) (Z.log2 + 1)
  have hZ1 : 1 <= Z := hZ
  rw [<- Finset.sum_filter, hFilter, ite_eq_left hZ1] at hSum
  exact hSum

theorem cutoff_sum_le (f : Nat -> Real) (Z : Nat) (hZ : 0 < Z)
    (hf : forall d, 0 <= f d) :
    (Finset.Icc 1 Z).sum f <=
      f 1 + (Finset.range (Z.log2 + 1)).sum
        (fun k => (Finset.Ioc (2 ^ k) (2 * 2 ^ k)).sum f) := by
  rw [cutoff_partition f Z hZ]
  apply add_le_add (le_refl (f 1))
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro d hd
  split_ifs
  . exact le_refl _
  . exact hf d

end PrimeFactorOscillations.QuadraticDyadicCover

