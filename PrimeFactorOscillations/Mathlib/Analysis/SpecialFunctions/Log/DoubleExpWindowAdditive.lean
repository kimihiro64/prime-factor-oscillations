/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Additive logarithmic windows around double exponentials -/

namespace Real

/-- A fixed multiplicative window about a double exponential lies in its log-log band. -/
theorem log_log_in_double_exp_window_additive {t x : Real} (ht : 8 <= t)
    (hlow : Real.exp (Real.exp t) / 2 <= x)
    (hhigh : x <= 8 * Real.exp (Real.exp t)) :
    t - Real.log 2 <= Real.log (Real.log x) /\
      Real.log (Real.log x) <= t + Real.log 2 := by
  have hexp : (9 : Real) <= Real.exp t := by linarith [Real.add_one_le_exp t]
  have hlog2 : Real.log 2 <= (2 : Real) := Real.log_le_self (by norm_num)
  have hlog8 : Real.log 8 <= (8 : Real) := Real.log_le_self (by norm_num)
  have hEpos := Real.exp_pos (Real.exp t)
  have hepos := Real.exp_pos t
  have hx : 0 < x := (div_pos hEpos (by norm_num)).trans_le hlow
  have hl := Real.log_le_log (div_pos hEpos (by norm_num)) hlow
  rw [Real.log_div (ne_of_gt hEpos) (by norm_num), Real.log_exp] at hl
  have hu := Real.log_le_log hx hhigh
  rw [Real.log_mul (by norm_num) (ne_of_gt hEpos), Real.log_exp] at hu
  have hloglow : Real.exp t / 2 <= Real.log x := by linarith
  have hloghigh : Real.log x <= 2 * Real.exp t := by linarith
  have hlogpos : 0 < Real.log x := (div_pos hepos (by norm_num)).trans_le hloglow
  have hllow := Real.log_le_log (div_pos hepos (by norm_num)) hloglow
  rw [Real.log_div (ne_of_gt hepos) (by norm_num), Real.log_exp] at hllow
  have hlhigh := Real.log_le_log hlogpos hloghigh
  rw [Real.log_mul (by norm_num) (ne_of_gt hepos), Real.log_exp] at hlhigh
  exact And.intro hllow (by simpa only [add_comm] using hlhigh)

end Real
