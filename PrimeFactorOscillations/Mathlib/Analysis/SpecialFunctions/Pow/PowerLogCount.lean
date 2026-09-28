/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # Extracting a power lower bound from logarithmic losses -/

open Filter

namespace Real

theorem eventually_const_mul_log_natpow_le_rpow (A : Real) (D : Nat)
    {s : Real} (hs : 0 < s) :
    Filter.Eventually (fun N : Nat => A * Real.log (N : Real) ^ D <= (N : Real) ^ s)
      Filter.atTop := by
  have ho := (_root_.isLittleO_log_rpow_rpow_atTop (D : Real) hs).const_mul_left A
  have hb := ho.bound (show (0 : Real) < 1 by norm_num)
  have hn := (tendsto_natCast_atTop_atTop (R := Real)).eventually hb
  filter_upwards [hn] with N hN
  simp only [Real.rpow_natCast, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) s)] at hN
  exact (le_abs_self _).trans hN

theorem eventually_cuberoot_le_of_power_log_bound (G : Nat -> Nat)
    (A alpha : Real) (D : Nat) (ha : alpha < 1 / 3)
    (hb : Filter.Eventually (fun N : Nat =>
      (N : Real) <= A * (G N : Real) * (N : Real) ^ (2 * alpha) *
        Real.log (N : Real) ^ D) Filter.atTop) :
    Filter.Eventually (fun N : Nat => (N : Real) ^ ((1 : Real) / 3) <= (G N : Real))
      Filter.atTop := by
  have hs : 0 < (2 : Real) / 3 - 2 * alpha := by linarith
  have hp := eventually_const_mul_log_natpow_le_rpow A D hs
  filter_upwards [hb, hp, Filter.eventually_ge_atTop 1] with N hN hpoly hN1
  have hpos : (0 : Real) < N := by exact_mod_cast hN1
  have hmul : A * (G N : Real) * (N : Real) ^ (2 * alpha) *
      Real.log (N : Real) ^ D <=
        (G N : Real) * (N : Real) ^ (2 * alpha) *
          (N : Real) ^ ((2 : Real) / 3 - 2 * alpha) := by
    calc
      _ = (G N : Real) * (N : Real) ^ (2 * alpha) *
          (A * Real.log (N : Real) ^ D) := by ring
      _ <= _ := mul_le_mul_of_nonneg_left hpoly
        (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hcancel : (N : Real) ^ (2 * alpha) *
      (N : Real) ^ ((2 : Real) / 3 - 2 * alpha) =
        (N : Real) ^ ((2 : Real) / 3) := by
    rw [<- Real.rpow_add hpos]
    congr 1
    ring
  have hprod : (N : Real) <= (G N : Real) * (N : Real) ^ ((2 : Real) / 3) := by
    have hm := hN.trans hmul
    rwa [mul_assoc, hcancel] at hm
  have hsplit : (N : Real) ^ ((1 : Real) / 3) * (N : Real) ^ ((2 : Real) / 3) =
      (N : Real) := by
    rw [<- Real.rpow_add hpos]
    norm_num
  by_contra hfail
  have hlt : (G N : Real) < (N : Real) ^ ((1 : Real) / 3) := lt_of_not_ge hfail
  have hstrict := _root_.mul_lt_mul_of_pos_right hlt
    (Real.rpow_pos_of_pos hpos ((2 : Real) / 3))
  exact (not_lt_of_ge (hsplit.le.trans hprod)) hstrict

end Real
