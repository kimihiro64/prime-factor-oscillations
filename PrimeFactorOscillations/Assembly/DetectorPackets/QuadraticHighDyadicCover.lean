/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.QuadraticDyadicCover

/-!
# QuadraticHighDyadicCover

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

namespace PrimeFactorOscillations.QuadraticHighDyadicCover

open QuadraticDyadicCover

theorem log2_mono_pos (Z V : Nat) (hZ : 0 < Z) (hZV : Z <= V) :
    Z.log2 <= V.log2 :=
  (Nat.le_log2 (Nat.ne_of_gt (hZ.trans_le hZV))).mpr
    ((cutoff_power_bound Z hZ).1.trans hZV)

theorem high_band_scale (Z V k : Nat) (hZ : 0 < Z) (hZV : Z <= V)
    (hk : Membership.mem (Finset.Icc Z.log2 V.log2) k) :
    Z < 2 * 2 ^ k /\ 2 ^ k <= V := by
  have hb := Finset.mem_Icc.mp hk
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
  constructor
  . rw [<- hpow]
    exact (cutoff_power_bound Z hZ).2.trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ hb.1))
  . exact (Nat.pow_le_pow_right (by decide) hb.2).trans
      (cutoff_power_bound V (hZ.trans_le hZV)).1

theorem high_sum_le (f : Nat -> Real) (Z V : Nat) (hZ : 0 < Z) (hZV : Z <= V)
    (hf : forall d, 0 <= f d) :
    (Finset.Ioc Z V).sum f <=
      (Finset.Icc Z.log2 V.log2).sum
        (fun k => (Finset.Ioc (2 ^ k) (2 * 2 ^ k)).sum f) := by
  classical
  have hV : 0 < V := hZ.trans_le hZV
  have hFilterD : (Finset.Icc 1 V).filter (fun d => Z < d) = Finset.Ioc Z V := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    . intro h
      exact And.intro h.2 h.1.2
    . intro h
      exact And.intro (And.intro
        (Nat.succ_le_of_lt ((Nat.zero_le Z).trans_lt h.1)) h.2) h.1
  have hFilterK :
      (Finset.range (V.log2 + 1)).filter (fun k => Z.log2 <= k) =
        Finset.Icc Z.log2 V.log2 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    . intro h
      exact And.intro h.2 (Nat.le_of_lt_succ h.1)
    . intro h
      exact And.intro (Nat.lt_succ_of_le h.2) h.1
  have hg (d : Nat) : 0 <= (if Z < d then f d else 0) := by
    split_ifs
    . exact hf d
    . exact le_refl _
  have hCover := cutoff_sum_le (fun d => if Z < d then f d else 0) V hV hg
  have hNot : Not (Z < 1) := not_lt_of_ge (show 1 <= Z from hZ)
  rw [<- Finset.sum_filter, hFilterD, ite_eq_right hNot, zero_add] at hCover
  apply hCover.trans
  calc
    _ <= (Finset.range (V.log2 + 1)).sum (fun k =>
        if Z.log2 <= k then (Finset.Ioc (2 ^ k) (2 * 2 ^ k)).sum f else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hkZ : Z.log2 <= k
      . rw [ite_eq_left hkZ]
        apply Finset.sum_le_sum
        intro d hd
        split_ifs
        . exact le_refl _
        . exact hf d
      . rw [ite_eq_right hkZ]
        have hkNext : k + 1 <= Z.log2 := Nat.succ_le_of_lt (lt_of_not_ge hkZ)
        have hUpper : 2 * 2 ^ k <= Z := by
          calc
            _ = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
            _ <= 2 ^ Z.log2 := Nat.pow_le_pow_right (by decide) hkNext
            _ <= Z := (cutoff_power_bound Z hZ).1
        have hZero : (Finset.Ioc (2 ^ k) (2 * 2 ^ k)).sum
            (fun d => if Z < d then f d else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro d hd
          exact ite_eq_right (not_lt_of_ge ((Finset.mem_Ioc.mp hd).2.trans hUpper))
        rw [hZero]
    _ = _ := by rw [<- Finset.sum_filter, hFilterK]

end PrimeFactorOscillations.QuadraticHighDyadicCover

