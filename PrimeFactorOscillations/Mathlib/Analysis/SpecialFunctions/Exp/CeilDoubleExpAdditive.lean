/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Floor.Ring
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.DoubleExpWindowAdditive

/-! # Natural ceiling windows preserve the additive logarithmic band -/

namespace Real

/-- Every actual prefix in the natural double-exponential window has the required band. -/
theorem ceil_double_exp_prime_prefix_additive_band {t : Real} (ht : 8 <= t) {p : Nat}
    (hlo : Nat.ceil (Real.exp (Real.exp t)) <= p)
    (hhi : p <= 4 * Nat.ceil (Real.exp (Real.exp t))) :
    t - Real.log 2 <= Real.log (Real.log (p - 1 : Nat)) /\
      Real.log (Real.log (p - 1 : Nat)) <= t + Real.log 2 := by
  have hEpos := Real.exp_pos (Real.exp t)
  have hE : (2 : Real) <= Real.exp (Real.exp t) := by
    linarith [Real.add_one_le_exp t, Real.add_one_le_exp (Real.exp t)]
  have hceil := Nat.le_ceil (Real.exp (Real.exp t))
  have hceilUpper := Nat.ceil_lt_add_one hEpos.le
  have hceilPos : 0 < Nat.ceil (Real.exp (Real.exp t)) := Nat.ceil_pos.mpr hEpos
  have hp1 : 1 <= p := by omega
  have hloR : (Nat.ceil (Real.exp (Real.exp t)) : Real) <= p := by exact_mod_cast hlo
  have hhiR : (p : Real) <= 4 * (Nat.ceil (Real.exp (Real.exp t)) : Real) := by
    exact_mod_cast hhi
  apply Real.log_log_in_double_exp_window_additive ht
  next =>
    rw [Nat.cast_sub hp1, Nat.cast_one]
    linarith
  next =>
    rw [Nat.cast_sub hp1, Nat.cast_one]
    linarith

end Real
