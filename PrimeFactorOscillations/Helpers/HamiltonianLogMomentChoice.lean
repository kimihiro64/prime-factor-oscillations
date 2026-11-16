/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # An explicit even logarithmic moment and its complete rounding budget -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_log_two_half : (1 : Real) / 2 <= Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 1 / 2)
  rw [one_div, Real.log_inv] at h
  norm_num at h
  linarith only [h]

theorem hamiltonian_log_four_lower : (1 : Real) <= Real.log 4 := by
  have hFour : Real.log (4 : Real) = 2 * Real.log 2 := by
    calc
      _ = Real.log ((2 : Real) * 2) := by norm_num
      _ = Real.log 2 + Real.log 2 := Real.log_mul (by norm_num) (by norm_num)
      _ = _ := by ring
  rw [hFour]
  nlinarith only [hamiltonian_log_two_half]

def hamiltonianLogMoment (n : Real) : Nat :=
  2 * Nat.ceil (2 * Real.log n)

theorem hamiltonian_even_logarithmic_moment
    (n : Real) (hn : 6 <= n) :
    2 <= hamiltonianLogMoment n /\
      Even (hamiltonianLogMoment n) /\
      ((hamiltonianLogMoment n).pred : Real) <= 5 * Real.log n /\
      n ^ (2 / (hamiltonianLogMoment n : Real)) <= 2 := by
  let k := Nat.ceil (2 * Real.log n)
  let p := hamiltonianLogMoment n
  have hnPos : 0 < n := by linarith only [hn]
  have hLog : 1 <= Real.log n :=
    hamiltonian_log_four_lower.trans
      (Real.log_le_log (by norm_num) (by linarith only [hn]))
  have hkL : 2 * Real.log n <= (k : Real) := Nat.le_ceil _
  have hkU : (k : Real) < 2 * Real.log n + 1 :=
    Nat.ceil_lt_add_one (by linarith only [hLog])
  have hpCast : (p : Real) = 2 * (k : Real) := by
    dsimp [p, k, hamiltonianLogMoment]
    rw [Nat.cast_mul, Nat.cast_ofNat]
  have hPL : 4 * Real.log n <= (p : Real) := by
    rw [hpCast]
    linarith only [hkL]
  have hPU : (p : Real) < 4 * Real.log n + 2 := by
    rw [hpCast]
    linarith only [hkU]
  have hpR : (2 : Real) <= p := by linarith only [hPL, hLog]
  have hp : 2 <= p := by exact_mod_cast hpR
  have hpNatPos : 0 < p := by omega
  have hpPos : (0 : Real) < p := by exact_mod_cast hpNatPos
  have hpNe : Not ((p : Real) = 0) := ne_of_gt hpPos
  have hEven : Even p := by
    exact Exists.intro k (by dsimp [p, hamiltonianLogMoment, k]; ring)
  have hPred : (p.pred : Real) + 1 = (p : Real) := by
    exact_mod_cast Nat.succ_pred_eq_of_pos hpNatPos
  have hPredBudget : (p.pred : Real) <= 5 * Real.log n := by
    linarith only [hPred, hPU, hLog]
  let w : Real := 1 / (2 * (p : Real))
  have hw : 0 <= w := div_nonneg (by norm_num) (mul_nonneg (by norm_num) hpPos.le)
  have hScaled := mul_le_mul_of_nonneg_right hPL hw
  have hLeft : (4 * Real.log n) * w = Real.log n * (2 / (p : Real)) := by
    dsimp [w]
    field_simp [hpNe] <;> ring
  have hRight : (p : Real) * w = 1 / 2 := by
    dsimp [w]
    field_simp [hpNe] <;> ring
  rw [hLeft, hRight] at hScaled
  have hPower : n ^ (2 / (p : Real)) <= 2 := by
    calc
      _ = Real.exp (Real.log n * (2 / (p : Real))) := Real.rpow_def_of_pos hnPos _
      _ <= Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr (hScaled.trans hamiltonian_log_two_half)
      _ = _ := Real.exp_log (by norm_num)
  exact And.intro hp (And.intro hEven (And.intro hPredBudget hPower))

theorem hamiltonian_rounding_log_geometry
    (m : Real) (hm : 1 <= m) :
    1 <= Real.log (4 * m) /\ Real.log (6 * m) <= 2 * Real.log (4 * m) := by
  have hm0 : 0 <= m := by linarith only [hm]
  have hL : 1 <= Real.log (4 * m) :=
    hamiltonian_log_four_lower.trans
      (Real.log_le_log (by norm_num) (by linarith only [hm]))
  have hSquare : 6 * m <= (4 * m) ^ 2 := by
    have hM := mul_le_mul_of_nonneg_right hm hm0
    nlinarith only [hM, hm]
  have hN : 0 < 6 * m := by linarith only [hm]
  have hLog := Real.log_le_log hN hSquare
  rw [Real.log_pow] at hLog
  exact And.intro hL (by simpa only [Nat.cast_ofNat] using hLog)

theorem hamiltonian_logarithmic_rounding_sqrt_bound
    (m d : Real) (hm : 1 <= m) (hd : 1 <= d) :
    Real.sqrt (1 + 8 * ((hamiltonianLogMoment (6 * m)).pred : Real) * d *
      (6 * m) ^ (2 / (hamiltonianLogMoment (6 * m) : Real))) <=
      16 * Real.sqrt (d * Real.log (4 * m)) := by
  have hChoice := hamiltonian_even_logarithmic_moment (6 * m) (by linarith only [hm])
  have hGeometry := hamiltonian_rounding_log_geometry m hm
  have hd0 : 0 <= d := by linarith only [hd]
  have hPred := hChoice.2.2.1
  have hPower := hChoice.2.2.2
  have hPower0 : 0 <= (6 * m) ^
      (2 / (hamiltonianLogMoment (6 * m) : Real)) :=
    Real.rpow_nonneg (by linarith only [hm]) _
  have hBase : d <= d * Real.log (4 * m) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hGeometry.1 hd0
  have hdL : 1 <= d * Real.log (4 * m) := hd.trans hBase
  have hScaled := mul_le_mul_of_nonneg_left hGeometry.2 hd0
  have hCoeff : 0 <= 8 * ((hamiltonianLogMoment (6 * m)).pred : Real) * d :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hd0
  have hPowerScaled := mul_le_mul_of_nonneg_left hPower hCoeff
  have hPredScaled := mul_le_mul_of_nonneg_right hPred
    (mul_nonneg (by norm_num : (0 : Real) <= 16) hd0)
  have hBudget :
      1 + 8 * ((hamiltonianLogMoment (6 * m)).pred : Real) * d *
        (6 * m) ^ (2 / (hamiltonianLogMoment (6 * m) : Real)) <=
        256 * (d * Real.log (4 * m)) := by
    calc
      _ <= 1 + 8 * ((hamiltonianLogMoment (6 * m)).pred : Real) * d * 2 :=
        add_le_add le_rfl hPowerScaled
      _ <= 1 + 8 * (5 * Real.log (6 * m)) * d * 2 := by
        nlinarith only [hPredScaled]
      _ <= 1 + 160 * d * Real.log (4 * m) := by nlinarith only [hScaled]
      _ <= _ := by nlinarith only [hdL]
  have h := Real.sqrt_le_sqrt hBudget
  rw [Real.sqrt_mul (by norm_num : (0 : Real) <= 256)] at h
  have h256 : Real.sqrt (256 : Real) = 16 := by
    have hSq := Real.sq_sqrt (by norm_num : (0 : Real) <= 256)
    have hNonneg := Real.sqrt_nonneg (256 : Real)
    nlinarith only [hSq, hNonneg]
  rw [h256] at h
  exact h

end PrimeFactorOscillations
