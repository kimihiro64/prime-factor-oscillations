/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact theta behavior on unit intervals

Elementary kernel bounds and the inclusive integer jump of Chebyshev theta.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Real

/-- An endpoint lower bound for the positive logarithmic tail kernel. -/
theorem one_div_sq_mul_log_le_tailKernel
    (s t : Real) (hs : 1 < s) (hst : s <= t) :
    1 / (t ^ 2 * log t) <= (1 / log s + 1 / (log s) ^ 2) / s ^ 2 := by
  have hsPos : 0 < s := lt_trans zero_lt_one hs
  have htPos : 0 < t := hsPos.trans_le hst
  have hLs : 0 < log s := log_pos hs
  have hLogs : log s <= log t := log_le_log hsPos hst
  have hSquares : s ^ 2 <= t ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hst) (add_nonneg htPos.le hsPos.le)
    nlinarith
  calc
    1 / (t ^ 2 * log t) = (1 / log t) / t ^ 2 := by ring
    _ <= (1 / log s) / t ^ 2 :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hLs hLogs) (sq_nonneg t)
    _ <= (1 / log s) / s ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hsPos) hSquares
    _ <= (1 / log s + 1 / (log s) ^ 2) / s ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg s)
      have hExtra : 0 <= 1 / (log s) ^ 2 := by positivity
      linarith

end Real

namespace Chebyshev

/-- A global elementary theta-error bound, using only Chebyshev's log-four bound. -/
theorem abs_theta_sub_self_le (t : Real) (ht : 0 <= t) :
    abs (theta t - t) <= t := by
  have hLogTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
  have hLogFour : Real.log 4 <= 2 := by
    rw [show (4 : Real) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (by norm_num)]
    linarith
  have hUpper := (theta_le_log4_mul_x ht).trans (mul_le_mul_of_nonneg_right hLogFour ht)
  have hLower := theta_nonneg t
  exact abs_le.mpr (And.intro (by linarith) (by linarith))

/-- Theta is exactly constant from an integer through the next open endpoint. -/
theorem theta_eq_nat_of_mem_Ico (n : Nat) (t : Real)
    (hLower : (n : Real) <= t) (hUpper : t < (n : Real) + 1) :
    theta t = theta (n : Real) := by
  have ht : 0 <= t := (Nat.cast_nonneg n).trans hLower
  have hFloor : Nat.floor t = n :=
    (Nat.floor_eq_iff ht).2 (And.intro hLower hUpper)
  rw [theta_eq_theta_coe_floor t, hFloor]

/-- The exact inclusive theta jump at the next integer. -/
theorem theta_nat_succ_sub (n : Nat) :
    theta ((n + 1 : Nat) : Real) - theta (n : Real) =
      if (n + 1).Prime then Real.log ((n + 1 : Nat) : Real) else 0 := by
  rw [theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log, Nat.primesLE_succ]
  split_ifs with hPrime
  . rw [Finset.sum_insert (Nat.notMem_primesLE n)]
    ring
  . simp

theorem theta_nat_succ_sub_le_log (n : Nat) :
    theta ((n + 1 : Nat) : Real) - theta (n : Real) <=
      Real.log ((n + 1 : Nat) : Real) := by
  rw [theta_nat_succ_sub]
  split_ifs
  . exact le_rfl
  . apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

/-- The exact theta-error integrand is at most two over the variable once log is one. -/
theorem theta_error_tailKernel_abs_le (t : Real) (ht : 0 < t)
    (hLog : 1 <= Real.log t) :
    abs ((theta t - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) <= 2 / t := by
  have hL : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hLog
  have hInv : 1 / Real.log t <= 1 := by
    calc
      1 / Real.log t <= 1 / (1 : Real) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLog
      _ = 1 := by norm_num
  have hLogSquare : 1 <= (Real.log t) ^ 2 := by nlinarith
  have hInvSquare : 1 / (Real.log t) ^ 2 <= 1 := by
    calc
      1 / (Real.log t) ^ 2 <= 1 / (1 : Real) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLogSquare
      _ = 1 := by norm_num
  have hKernel : 0 <= (1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2 := by
    positivity
  have hKernelUpper :
      (1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2 <= 2 / t ^ 2 := by
    exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg t)
  rw [abs_mul, abs_of_nonneg hKernel]
  calc
    abs (theta t - t) *
        ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2) <= t * (2 / t ^ 2) :=
      mul_le_mul (abs_theta_sub_self_le t ht.le) hKernelUpper hKernel ht.le
    _ = 2 / t := by field_simp [ht.ne']

end Chebyshev
