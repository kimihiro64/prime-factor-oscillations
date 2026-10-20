/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Explicit linear logarithm bounds used by a finite cutoff certificate. -/

set_option autoImplicit false
set_option Elab.async false

namespace Real

theorem log_five_le_nine_fifths : Real.log 5 <= (9 / 5 : Real) := by
  have hp : (5 : Real) <= ((6 : Real) / 5) ^ 9 := by norm_num
  have hl := Real.log_le_log (show (0 : Real) < 5 by norm_num) hp
  rw [Real.log_pow] at hl
  have hr := Real.log_le_sub_one_of_pos (show (0 : Real) < (6 : Real) / 5 by norm_num)
  norm_num at hl hr
  linarith

theorem log_nat_le_nine_twenty_fifths_mul (z : Nat) (hz : 5 <= z) :
    Real.log (z : Real) <= (9 / 25 : Real) * (z : Real) := by
  have hzR : (5 : Real) <= (z : Real) := by exact_mod_cast hz
  have hzPos : (0 : Real) < (z : Real) := by linarith only [hzR]
  have h := Real.log_le_sub_one_of_pos (div_pos hzPos (by norm_num : (0 : Real) < 5))
  rw [Real.log_div (ne_of_gt hzPos) (by norm_num)] at h
  linarith [log_five_le_nine_fifths]

end Real
