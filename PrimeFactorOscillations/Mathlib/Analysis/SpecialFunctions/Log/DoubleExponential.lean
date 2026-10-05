/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.IteratedRemainder

/-!
# Double logarithms of counts at a double-exponential scale

A coarse multiplicative count envelope gives an explicit exponentially
small error after two logarithms. Positivity of both logarithms is retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Real

/-- Coarse bounds between exp(exp(v))/(2 exp(v)) and exp(exp(v)) suffice
for an explicit double-logarithm error, uniformly for v at least sixteen. -/
theorem logLog_exp_exp_envelope (b v : Real) (hv : 16 <= v)
    (hlower : exp (exp v) / (2 * exp v) <= b)
    (hupper : b <= exp (exp v)) :
    1 < b /\ abs (log (log b) - v) <= 4 * v / exp v := by
  have hv0 : 0 <= v := by linarith
  have hw : 0 < exp v := exp_pos _
  have hb : 0 < b := (div_pos (exp_pos _) (by positivity)).trans_le hlower
  have hlog2 : log 2 <= v := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith only [h, hv]
  have hlogLower : exp v - 2 * v <= log b := by
    have h := log_le_log (div_pos (exp_pos (exp v))
      (by positivity : (0 : Real) < 2 * exp v)) hlower
    rw [log_div (exp_pos _).ne' (by positivity : Not (2 * exp v = 0)),
      log_exp, log_mul (by norm_num : Not ((2 : Real) = 0)) hw.ne', log_exp] at h
    linarith only [h, hlog2]
  have hhalf : v / 2 <= exp (v / 2) := by linarith only [add_one_le_exp (v / 2)]
  have hquad : v ^ 2 <= 4 * exp v := by
    have hprod := mul_nonneg (sub_nonneg.mpr hhalf)
      (add_nonneg (exp_pos (v / 2)).le (by positivity : 0 <= v / 2))
    have heq : exp (v / 2) ^ 2 = exp v := by
      rw [pow_two, <- exp_add]
      congr 1
      ring
    nlinarith only [hprod, heq]
  have hfour : 4 * v <= exp v := by
    have hprod := mul_nonneg (by linarith : 0 <= v - 16) hv0
    nlinarith only [hprod, hquad]
  have hlogHalf : exp v / 2 <= log b := by linarith only [hlogLower, hfour]
  have hlogPos : 0 < log b := (div_pos hw (by norm_num)).trans_le hlogHalf
  have hb1 : 1 < b := by
    have h := exp_lt_exp.mpr hlogPos
    simpa only [exp_zero, exp_log hb] using h
  have hlogUpper : log b <= exp v := by
    simpa only [log_exp] using log_le_log hb hupper
  have hloglogUpper : log (log b) <= v := by
    simpa only [log_exp] using log_le_log hlogPos hlogUpper
  have hslope : v - log (log b) <= exp v / log b - 1 := by
    have h := log_le_sub_one_of_pos (div_pos hw hlogPos)
    rw [log_div hw.ne' hlogPos.ne', log_exp] at h
    exact h
  refine And.intro hb1 ?_
  rw [abs_of_nonpos (sub_nonpos.mpr hloglogUpper), neg_sub]
  calc
    v - log (log b) <= exp v / log b - 1 := hslope
    _ = (exp v - log b) / log b := by field_simp
    _ <= (2 * v) / log b :=
      div_le_div_of_nonneg_right (by linarith only [hlogLower]) hlogPos.le
    _ <= (2 * v) / (exp v / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlogHalf
    _ = 4 * v / exp v := by ring

end Real
