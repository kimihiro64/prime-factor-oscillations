/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Fixed multiplicities preserve strict double-exponential growth margins -/

set_option autoImplicit false
set_option Elab.async false

namespace Real

/-- A fixed multiplicity and additive unit are absorbed by every strict
increase in a nonnegative double-exponential growth coefficient. -/
theorem eventually_mul_double_exp_add_one_le
    (a b C : Real) (ha : 0 <= a) (hab : a < b) (hC : 0 <= C) :
    exists K : Nat, forall k : Nat, K <= k ->
      C * (Real.exp (Real.exp (a * k)) + 1) <=
        Real.exp (Real.exp (b * k)) := by
  let D : Real := 2 * max 1 C
  have hmax : (1 : Real) <= max 1 C := le_max_left _ _
  have hD : 0 < D := by dsimp only [D]; positivity
  have hdelta : 0 < b - a := sub_pos.mpr hab
  choose K hK using exists_nat_gt (Real.log D / (b - a))
  refine Exists.intro K ?_
  intro k hk
  have hkR : (K : Real) <= k := by exact_mod_cast hk
  have hquot : Real.log D / (b - a) <= k := (le_of_lt hK).trans hkR
  have hscale : Real.log D <= (b - a) * k := by
    have h := mul_le_mul_of_nonneg_right hquot hdelta.le
    have hc : (Real.log D / (b - a)) * (b - a) = Real.log D := by
      field_simp [ne_of_gt hdelta]
    rw [hc] at h
    simpa only [mul_comm] using h
  have hak : 0 <= a * k := mul_nonneg ha (Nat.cast_nonneg k)
  have hdk : 0 <= (b - a) * k := mul_nonneg hdelta.le (Nat.cast_nonneg k)
  have hx : 1 <= Real.exp (a * k) := by
    linarith only [Real.add_one_le_exp (a * k), hak]
  have hy := Real.add_one_le_exp ((b - a) * k)
  have hprod := mul_le_mul_of_nonneg_left hy (Real.exp_pos (a * k)).le
  have hreserve := mul_nonneg (show 0 <= Real.exp (a * k) - 1 by linarith) hdk
  have hinner : Real.log D + Real.exp (a * k) <= Real.exp (b * k) := by
    rw [show b * k = a * k + (b - a) * k by ring, Real.exp_add]
    nlinarith only [hprod, hreserve, hscale]
  have he := Real.exp_le_exp.mpr hinner
  rw [Real.exp_add, Real.exp_log hD] at he
  have hE : 1 <= Real.exp (Real.exp (a * k)) := by
    linarith only [Real.add_one_le_exp (Real.exp (a * k)), Real.exp_pos (a * k)]
  have hCM : C <= max 1 C := le_max_right _ _
  have hfirst : C * (Real.exp (Real.exp (a * k)) + 1) <=
      C * (2 * Real.exp (Real.exp (a * k))) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have hsecond := mul_le_mul_of_nonneg_right hCM
    (show 0 <= 2 * Real.exp (Real.exp (a * k)) by positivity)
  have hlast : C * (Real.exp (Real.exp (a * k)) + 1) <=
      D * Real.exp (Real.exp (a * k)) := by
    dsimp only [D]
    nlinarith only [hfirst, hsecond]
  exact hlast.trans he

/-- Fixed finite losses in a lower count preserve each smaller nonnegative
double-exponential coefficient. -/
theorem eventually_double_exp_le_of_mul_count
    (a b C : Real) (ha : 0 <= a) (hab : a < b) (hC : 0 < C) :
    exists K : Nat, forall k : Nat, K <= k -> forall m : Real,
      Real.exp (Real.exp (b * k)) <= C * (m + 1) ->
      Real.exp (Real.exp (a * k)) <= m := by
  choose K hK using eventually_mul_double_exp_add_one_le a b C ha hab hC.le
  refine Exists.intro K ?_
  intro k hk m hcount
  have hle := (hK k hk).trans hcount
  by_contra hn
  have hgt : m < Real.exp (Real.exp (a * k)) := lt_of_not_ge hn
  have hlt := mul_lt_mul_of_pos_left (_root_.add_lt_add_right hgt 1) hC
  exact (not_lt_of_ge hle) (by simpa only [add_comm] using hlt)

end Real
