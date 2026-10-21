/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact terminal grouping of finite ordered blocks

The rounded rank clock selects the end of each full group and the end
of the final shorter group. Its natural increments have bounded size,
preserve total mass and have a one-sided bounded prefix discrepancy.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

def groupedPrefix (n h m : Nat) : Nat :=
  if m < n then h * (m / h) else n

def groupedTerminalWeight (n h i : Nat) : Nat :=
  groupedPrefix n h (i + 1) - groupedPrefix n h i

theorem groupedPrefix_zero (n h : Nat) : groupedPrefix n h 0 = 0 := by
  by_cases hn : 0 < n
  next => simp [groupedPrefix, hn]
  next =>
    have he : n = 0 := by omega
    simp [groupedPrefix, he]

theorem groupedPrefix_end (n h : Nat) : groupedPrefix n h n = n := by
  simp [groupedPrefix]

theorem groupedPrefix_mono (n h : Nat) : Monotone (groupedPrefix n h) := by
  intro a b hab
  by_cases hb : b < n
  next =>
    have ha : a < n := lt_of_le_of_lt hab hb
    simpa only [groupedPrefix, ite_eq_left ha, ite_eq_left hb] using
      (Nat.mul_le_mul_left h (Nat.div_le_div_right hab))
  next =>
    by_cases ha : a < n
    next =>
      simp only [groupedPrefix, ite_eq_left ha, ite_eq_right hb]
      have hm : h * (a / h) <= a := Nat.le.intro (Nat.div_add_mod a h)
      exact le_trans hm (Nat.le_of_lt ha)
    next =>
      simp only [groupedPrefix, ite_eq_right ha, ite_eq_right hb]
      exact Nat.le_refl n

theorem groupedPrefix_step_le (n h i : Nat) (hh : 0 < h) :
    groupedPrefix n h (i + 1) <= groupedPrefix n h i + h := by
  by_cases hi : i < n
  next =>
    have hmax : i + 1 <= h * (i / h) + h := by
      have hm := Nat.mod_lt i hh
      have he := Nat.div_add_mod i h
      omega
    by_cases hs : i + 1 < n
    next =>
      have hadd : i + 1 <= i + h := by omega
      have hd : (i + 1) / h <= (i + h) / h := Nat.div_le_div_right hadd
      rw [Nat.add_div_right i hh] at hd
      have hm := Nat.mul_le_mul_left h hd
      simpa only [groupedPrefix, ite_eq_left hi, ite_eq_left hs,
        Nat.mul_add, Nat.mul_one] using hm
    next =>
      have he : i + 1 = n := by omega
      rw [he] at hmax
      simpa only [groupedPrefix, ite_eq_left hi, ite_eq_right hs] using hmax
  next =>
    have hs : Not (i + 1 < n) := by omega
    simp only [groupedPrefix, ite_eq_right hi, ite_eq_right hs]
    omega

theorem groupedTerminalWeight_le (n h i : Nat) (hh : 0 < h) :
    groupedTerminalWeight n h i <= h := by
  have hs := groupedPrefix_step_le n h i hh
  unfold groupedTerminalWeight
  omega

/-- The rounded rank clock is exactly the prefix sum of terminal group weights. -/
theorem groupedPrefix_sum (n h m : Nat) :
    (Finset.range m).sum (groupedTerminalWeight n h) = groupedPrefix n h m := by
  induction m with
  | zero =>
      simpa only [Finset.range_zero, Finset.sum_empty] using
        (groupedPrefix_zero n h).symm
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      change groupedPrefix n h m +
        (groupedPrefix n h (m + 1) - groupedPrefix n h m) =
          groupedPrefix n h (m + 1)
      have hs : groupedPrefix n h m <= groupedPrefix n h (m + 1) :=
        groupedPrefix_mono n h (Nat.le_succ m)
      exact (Nat.add_comm _ _).trans (Nat.sub_add_cancel hs)

theorem groupedTerminalWeight_total (n h : Nat) :
    (Finset.range n).sum (groupedTerminalWeight n h) = n := by
  rw [groupedPrefix_sum, groupedPrefix_end]

theorem groupedPrefix_remainder (n h m : Nat) (hm : m < n) :
    (Finset.range m).sum (groupedTerminalWeight n h) + m % h = m := by
  rw [groupedPrefix_sum]
  simpa only [groupedPrefix, ite_eq_left hm] using Nat.div_add_mod m h

/-- Every prefix has nonpositive signed discrepancy and deficit strictly below the cap. -/
theorem groupedPrefix_balance (n h m : Nat) (hh : 0 < h) (hm : m <= n) :
    And ((Finset.range m).sum (groupedTerminalWeight n h) <= m)
      (m - (Finset.range m).sum (groupedTerminalWeight n h) < h) := by
  by_cases hlt : m < n
  next =>
    have he := groupedPrefix_remainder n h m hlt
    have hr := Nat.mod_lt m hh
    constructor <;> omega
  next =>
    have he : m = n := by omega
    rw [he, groupedTerminalWeight_total]
    exact And.intro (Nat.le_refl n) (by omega)

/-- The actual signed prefix error, including the completed endpoint, is in [1-h, 0]. -/
theorem groupedPrefix_signed_balance (n h m : Nat) (hh : 0 < h) (hm : m <= n) :
    And (-((h : Int) - 1) <=
      (((Finset.range m).sum (groupedTerminalWeight n h) : Nat) : Int) - (m : Int))
      ((((Finset.range m).sum (groupedTerminalWeight n h) : Nat) : Int) -
        (m : Int) <= 0) := by
  have hb := groupedPrefix_balance n h m hh hm
  omega

end Nat
