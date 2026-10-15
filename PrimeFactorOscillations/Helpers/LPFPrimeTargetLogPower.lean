/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrimeTargetMoment

/-! # Complete growing-moment error with any fixed logarithmic power -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private theorem eventually_log_power_moment_budget (L : Nat) (C : Real) (hC : 0 < C) :
    Filter.Eventually (fun t : Real => forall q : Nat,
      (q : Real) <= 10 * Real.log t ->
      Real.log C + (L : Real) * Real.log t + (q : Real) * Real.log (C * Real.log t) <=
        (1 / 16 : Real) * t) Filter.atTop := by
  let K := abs (Real.log C) + (L : Real) + 10 * C
  have hK : 0 <= K := by dsimp [K]; positivity
  have hSmall := (Real.isLittleO_pow_log_id_atTop (n := 2)).const_mul_left K
  filter_upwards [hSmall.bound (by norm_num : (0 : Real) < 1 / 16),
    Filter.eventually_ge_atTop (1 : Real),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : Real))]
    with t hBound ht hLog
  have ht0 : 0 <= t := by linarith
  have hProduct : 0 < C * Real.log t := mul_pos hC (by linarith)
  have hLogBound : Real.log (C * Real.log t) <= C * Real.log t := by
    have h := Real.log_le_sub_one_of_pos hProduct
    linarith
  have hBound' : K * Real.log t ^ 2 <= (1 / 16 : Real) * t := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (sq_nonneg _)),
      id_eq, abs_of_nonneg ht0] using hBound
  intro q hq
  have hTerm : (q : Real) * Real.log (C * Real.log t) <= 10 * C * Real.log t ^ 2 := by
    calc
      _ <= (q : Real) * (C * Real.log t) :=
        mul_le_mul_of_nonneg_left hLogBound (Nat.cast_nonneg q)
      _ <= (10 * Real.log t) * (C * Real.log t) :=
        mul_le_mul_of_nonneg_right hq hProduct.le
      _ = _ := by ring
  have hSq : 1 <= Real.log t ^ 2 := by nlinarith only [hLog]
  have hConst : abs (Real.log C) <= abs (Real.log C) * Real.log t ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hSq (abs_nonneg (Real.log C))
  have hLinear : (L : Real) * Real.log t <= (L : Real) * Real.log t ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith only [hLog]) (Nat.cast_nonneg L)
  calc
    _ <= abs (Real.log C) * Real.log t ^ 2 + (L : Real) * Real.log t ^ 2 +
        10 * C * Real.log t ^ 2 :=
      _root_.add_le_add (_root_.add_le_add
        ((le_abs_self (Real.log C)).trans hConst) hLinear) hTerm
    _ = K * Real.log t ^ 2 := by dsimp [K]; ring
    _ <= _ := hBound'

/-- Any fixed logarithmic loss is harmless uniformly over the required moment range. -/
theorem eventually_complete_moment_error_log_power_le (L : Nat) (C : Real) (hC : 0 < C) :
    Filter.Eventually (fun X : Real => forall q : Nat,
      (q : Real) <= 10 * Real.log (Real.log X) ->
      C * X ^ (7 / 8 : Real) * Real.log X ^ L *
        (C * Real.log (Real.log X)) ^ q <= X ^ (15 / 16 : Real)) Filter.atTop := by
  have hBudget := Real.tendsto_log_atTop.eventually
    (eventually_log_power_moment_budget L C hC)
  have hLogLog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (Filter.eventually_ge_atTop (1 : Real))
  filter_upwards [hBudget, hLogLog, Filter.eventually_ge_atTop (2 : Real)]
    with X hBudget hLogLog hX2
  change 1 <= Real.log (Real.log X) at hLogLog
  intro q hq
  have hX : 0 < X := by linarith
  have hLogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hLL : 0 < Real.log (Real.log X) := by linarith
  have hBase : 0 < C * Real.log (Real.log X) := mul_pos hC hLL
  have hLeft : 0 < C * X ^ (7 / 8 : Real) * Real.log X ^ L *
      (C * Real.log (Real.log X)) ^ q := by positivity
  have hRight : 0 < X ^ (15 / 16 : Real) := Real.rpow_pos_of_pos hX _
  apply (Real.log_le_log_iff hLeft hRight).mp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hX, Real.log_pow, Real.log_pow, Real.log_rpow hX]
  have h := hBudget q hq
  norm_num only [Nat.cast_ofNat] at *
  linarith only [h]

end PrimeFactorOscillations.LPF
