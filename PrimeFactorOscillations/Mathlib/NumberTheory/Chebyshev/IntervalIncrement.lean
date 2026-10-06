/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Chebyshev.UnitInterval

/-!
# Elementary theta increments from an integer anchor

Summing the exact prime jumps bounds theta over a finite real interval.
The last result controls both signs of its error on a subsequent window.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Chebyshev

/-- Summing integer prime jumps costs at most one logarithm per step. -/
theorem theta_nat_add_sub_le_mul_log (n d : Nat) (T : Real)
    (hT : ((n + d : Nat) : Real) <= T) :
    theta ((n + d : Nat) : Real) - theta (n : Real) <= (d : Real) * Real.log T := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hPrev : ((n + d : Nat) : Real) <= T := by
      have hCast : ((n + d : Nat) : Real) <= ((n + (d + 1) : Nat) : Real) := by
        exact_mod_cast (show n + d <= n + (d + 1) by omega)
      exact hCast.trans hT
    have hI := ih hPrev
    have hStep := theta_nat_succ_sub_le_log (n + d)
    have hLogs : Real.log (((n + d) + 1 : Nat) : Real) <= Real.log T :=
      Real.log_le_log (by positivity) (by simpa only [Nat.add_succ] using hT)
    simp only [Nat.cast_add, Nat.cast_one] at hI hStep hLogs hT
    simp only [Nat.cast_add, Nat.cast_succ, <- add_assoc]
    nlinarith only [hI, hStep, hLogs]

/-- A real endpoint has no larger theta increment than its interval length
multiplied by the endpoint logarithm. -/
theorem theta_sub_nat_le_interval_log (n : Nat) (hn : 1 <= n) (t : Real)
    (hnt : (n : Real) <= t) :
    theta t - theta (n : Real) <= (t - n) * Real.log t := by
  have ht : 0 <= t := (Nat.cast_nonneg n).trans hnt
  have hFloor : n <= Nat.floor t := Nat.le_floor hnt
  have hNat : n + (Nat.floor t - n) = Nat.floor t := Nat.add_sub_of_le hFloor
  have hBase := theta_nat_add_sub_le_mul_log n (Nat.floor t - n) t
    (by rw [hNat]; exact Nat.floor_le ht)
  rw [hNat] at hBase
  have hLength : ((Nat.floor t - n : Nat) : Real) <= t - n := by
    rw [Nat.cast_sub hFloor]
    linarith [Nat.floor_le ht]
  have hLog : 0 <= Real.log t := Real.log_nonneg
    ((show (1 : Real) <= n by exact_mod_cast hn).trans hnt)
  rw [theta_eq_theta_coe_floor t]
  exact hBase.trans (mul_le_mul_of_nonneg_right hLength hLog)

/-- An integer anchor with nonnegative theta error controls a whole
subsequent window using only the exact prime jumps. -/
theorem theta_error_abs_le_of_nat_window
    (n : Nat) (hn : 3 <= n) (h t : Real)
    (hLog : 1 <= Real.log (n : Real))
    (hE : 0 <= theta (n : Real) - n)
    (hh : 0 <= h) (hhN : h <= n)
    (htLower : (n : Real) <= t) (htUpper : t <= n + h) :
    abs (theta t - t) <= theta (n : Real) - n + 3 * h * Real.log (n : Real) := by
  have hnPos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have htPos : 0 < t := hnPos.trans_le htLower
  have hLPos : 0 <= Real.log (n : Real) := by linarith
  have hMono := theta_mono htLower
  have hJump := theta_sub_nat_le_interval_log n (by omega) t htLower
  have hLogTwo : Real.log (2 : Real) <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hLogT : Real.log t <= 2 * Real.log (n : Real) := by
    have h := Real.log_le_log htPos (show t <= 2 * (n : Real) by linarith)
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hnPos.ne'] at h
    linarith
  have hLogTNonneg : 0 <= Real.log t := Real.log_nonneg (by
    have hnThree : (3 : Real) <= n := by exact_mod_cast hn
    linarith)
  have hProduct : (t - n) * Real.log t <= h * (2 * Real.log (n : Real)) :=
    mul_le_mul (by linarith) hLogT hLogTNonneg hh
  have hhLog : h <= h * Real.log (n : Real) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hLog hh
  have hNonneg : 0 <= h * Real.log (n : Real) := mul_nonneg hh hLPos
  apply abs_le.mpr
  constructor <;> nlinarith only [hMono, hJump, hProduct, hE, hhLog,
    hNonneg, htUpper, htLower]

end Chebyshev

