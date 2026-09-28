/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Pow.CeilDoubleExpCount

/-! # Positive-power counts absorb fixed finite losses -/

namespace Real

/-- Any fixed positive-power count absorbs a fixed finite multiplicity loss. -/
theorem half_power_le_of_positive_power_count {X B m delta : Real}
    (hX : 1 <= X) (hd : 0 < delta) (hB : 0 < B)
    (hsize : 4 * B <= X ^ (delta / 2))
    (hcount : X ^ delta <= 2 * B * (m + 1)) :
    X ^ (delta / 2) <= m := by
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hpower : 1 <= X ^ (delta / 2) :=
    Real.one_le_rpow hX (by positivity)
  have hprod := mul_le_mul_of_nonneg_left hsize
    (Real.rpow_nonneg hXpos.le (delta / 2))
  have heq : X ^ (delta / 2) * X ^ (delta / 2) = X ^ delta := by
    rw [<- Real.rpow_add hXpos]
    congr 1
    ring
  rw [heq] at hprod
  by_contra hn
  have hm : m < X ^ (delta / 2) := lt_of_not_ge hn
  have hdiff : 0 < 2 * X ^ (delta / 2) - m - 1 := by linarith
  have hpositive := mul_pos hB hdiff
  nlinarith only [hpositive, hprod, hcount]

/-- A positive power of the double-exponential scale costs only a fixed
additive amount in the inner exponent. -/
theorem double_exp_le_rpow_ceil_of_margin {s t delta : Real}
    (hd : 0 < delta) (hgap : s + Real.log (2 / delta) <= t) :
    Real.exp (Real.exp s) <=
      (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ (delta / 2) := by
  have hcoef : 0 < 2 / delta := div_pos (by norm_num) hd
  have h := Real.exp_le_exp.mpr hgap
  rw [Real.exp_add, Real.exp_log hcoef] at h
  have hscaled := mul_le_mul_of_nonneg_right h hd.le
  have hcancel : (Real.exp s * (2 / delta)) * delta = 2 * Real.exp s := by
    field_simp [ne_of_gt hd]
  rw [hcancel] at hscaled
  have hexponents : Real.exp s <= Real.exp t * (delta / 2) := by
    nlinarith only [hscaled]
  calc
    Real.exp (Real.exp s) <= Real.exp (Real.exp t * (delta / 2)) :=
      Real.exp_le_exp.mpr hexponents
    _ = Real.exp (Real.exp t) ^ (delta / 2) := by rw [<- Real.exp_mul]
    _ <= (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ (delta / 2) :=
      Real.rpow_le_rpow (Real.exp_pos (Real.exp t)).le
        (Nat.le_ceil (Real.exp (Real.exp t))) (by positivity)

/-- A generous linear threshold provides the required positive-power reserve. -/
theorem rpow_ceil_double_exp_ge_linear (t delta : Real) (hd : 0 <= delta) :
    delta * t / 2 <=
      (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ (delta / 2) := by
  have ht : t <= Real.exp t := by linarith [Real.add_one_le_exp t]
  have hprod := mul_le_mul_of_nonneg_left ht (show 0 <= delta / 2 by positivity)
  have hlinear : delta * t / 2 <= Real.exp (Real.exp t * (delta / 2)) := by
    nlinarith only [hprod, Real.add_one_le_exp (Real.exp t * (delta / 2))]
  calc
    delta * t / 2 <= Real.exp (Real.exp t * (delta / 2)) := hlinear
    _ = Real.exp (Real.exp t) ^ (delta / 2) := by rw [<- Real.exp_mul]
    _ <= (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ (delta / 2) :=
      Real.rpow_le_rpow (Real.exp_pos (Real.exp t)).le
        (Nat.le_ceil (Real.exp (Real.exp t))) (by positivity)

/-- Arbitrary fixed positive-power supply preserves every smaller rank rate. -/
theorem double_exp_le_of_ceil_positive_power_count {s t B m delta : Real}
    (hd : 0 < delta) (hgap : s + Real.log (2 / delta) <= t)
    (hB : 0 < B) (hlarge : 8 * B <= delta * t)
    (hcount : (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ delta <=
      2 * B * (m + 1)) : Real.exp (Real.exp s) <= m := by
  have hceilpos : 0 < Nat.ceil (Real.exp (Real.exp t)) :=
    Nat.ceil_pos.mpr (Real.exp_pos (Real.exp t))
  have hX : (1 : Real) <= Nat.ceil (Real.exp (Real.exp t)) := by
    exact_mod_cast (show 1 <= Nat.ceil (Real.exp (Real.exp t)) by omega)
  have hsize : 4 * B <=
      (Nat.ceil (Real.exp (Real.exp t)) : Real) ^ (delta / 2) :=
    (show 4 * B <= delta * t / 2 by linarith).trans
      (rpow_ceil_double_exp_ge_linear t delta hd.le)
  exact (double_exp_le_rpow_ceil_of_margin hd hgap).trans
    (half_power_le_of_positive_power_count hX hd hB hsize hcount)

end Real
