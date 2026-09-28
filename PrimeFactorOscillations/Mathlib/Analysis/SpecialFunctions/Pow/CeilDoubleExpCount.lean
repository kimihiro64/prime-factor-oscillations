/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Absorbing a fixed counting loss at double-exponential scale -/

namespace Real

/-- A fixed finite fiber loss is absorbed by the difference of the two powers. -/
theorem quarter_power_le_of_cuberoot_count {X B m : Real} (hX : 1 <= X)
    (hB : 0 < B) (hsize : 4 * B <= X ^ ((1 : Real) / 12))
    (hcount : X ^ ((1 : Real) / 3) <= 2 * B * (m + 1)) :
    X ^ ((1 : Real) / 4) <= m := by
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hpower : 1 <= X ^ ((1 : Real) / 4) := Real.one_le_rpow hX (by norm_num)
  have hprod := mul_le_mul_of_nonneg_left hsize
    (Real.rpow_nonneg hXpos.le ((1 : Real) / 4))
  have heq : X ^ ((1 : Real) / 4) * X ^ ((1 : Real) / 12) =
      X ^ ((1 : Real) / 3) := by
    rw [<- Real.rpow_add hXpos]
    norm_num
  rw [heq] at hprod
  by_contra hn
  have hm : m < X ^ ((1 : Real) / 4) := lt_of_not_ge hn
  have hdiff : 0 < 2 * X ^ ((1 : Real) / 4) - m - 1 := by linarith
  have hpositive := mul_pos hB hdiff
  nlinarith only [hpositive, hprod, hcount]

/-- The natural double-exponential scale's quarter power dominates a half-rate scale. -/
theorem double_exp_half_le_quarter_power_ceil {t : Real} (ht : 8 <= t) :
    Real.exp (Real.exp (t / 2)) <=
      (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ ((1 : Real) / 4) := by
  have hz : (4 : Real) <= Real.exp (t / 2) := by linarith [Real.add_one_le_exp (t / 2)]
  have hsquare : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
    rw [<- Real.exp_add]
    congr 1
    ring
  have hprod := mul_le_mul_of_nonneg_right hz (Real.exp_pos (t / 2)).le
  have hexponents : Real.exp (t / 2) <= Real.exp t / 4 := by nlinarith only [hsquare, hprod]
  calc
    Real.exp (Real.exp (t / 2)) <= Real.exp (Real.exp t / 4) :=
      Real.exp_le_exp.mpr hexponents
    _ = Real.exp (Real.exp t) ^ ((1 : Real) / 4) := by
      rw [<- Real.exp_mul]
      congr 1
      ring
    _ <= (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ ((1 : Real) / 4) :=
      Real.rpow_le_rpow (Real.exp_pos (Real.exp t)).le
        (Nat.le_ceil (Real.exp (Real.exp t))) (by norm_num)

/-- A deliberately generous linear threshold suffices for the twelfth-power reserve. -/
theorem twelfth_power_ceil_double_exp_ge_linear (t : Real) :
    t / 12 <= (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ ((1 : Real) / 12) := by
  have hlinear : t / 12 <= Real.exp (Real.exp t / 12) := by
    linarith [Real.add_one_le_exp t, Real.add_one_le_exp (Real.exp t / 12)]
  calc
    t / 12 <= Real.exp (Real.exp t / 12) := hlinear
    _ = Real.exp (Real.exp t) ^ ((1 : Real) / 12) := by
      rw [<- Real.exp_mul]
      congr 1
      ring
    _ <= (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ ((1 : Real) / 12) :=
      Real.rpow_le_rpow (Real.exp_pos (Real.exp t)).le
        (Nat.le_ceil (Real.exp (Real.exp t))) (by norm_num)

/-- Exact finite count loss implies the desired double-exponential number of witnesses. -/
theorem double_exp_half_le_of_ceil_cuberoot_count {t B m : Real}
    (ht : 8 <= t) (hB : 0 < B) (hlarge : 48 * B <= t)
    (hcount : (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ ((1 : Real) / 3) <=
      2 * B * (m + 1)) : Real.exp (Real.exp (t / 2)) <= m := by
  have hceilpos : 0 < Nat.ceil (Real.exp (Real.exp t)) :=
    Nat.ceil_pos.mpr (Real.exp_pos (Real.exp t))
  have hX : (1 : Real) <= Nat.ceil (Real.exp (Real.exp t)) := by
    exact_mod_cast (show 1 <= Nat.ceil (Real.exp (Real.exp t)) by omega)
  have hsize : 4 * B <=
      (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ ((1 : Real) / 12) :=
    (show 4 * B <= t / 12 by linarith).trans (twelfth_power_ceil_double_exp_ge_linear t)
  exact (double_exp_half_le_quarter_power_ceil ht).trans
    (quarter_power_le_of_cuberoot_count hX hB hsize hcount)

end Real
