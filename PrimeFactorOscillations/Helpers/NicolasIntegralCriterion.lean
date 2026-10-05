/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasIntegerExcursions
import PrimeFactorOscillations.Helpers.NicolasNegativeLimit

/-!
# The corrected theta-tail integral criterion

The prime-square subtraction makes the integral eventually negative under RH.
The reflected Landau excursions prove the converse, at real and integer cutoffs.
The final statement displays the actual integral rather than a proxy function.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter MeasureTheory Set Robin1984

theorem eventually_nicolasK_neg_of_RH (hRH : RiemannHypothesis) :
    Filter.Eventually (fun x : Real => nicolasK x < 0) atTop := by
  have hMain : Filter.Eventually (fun x : Real =>
      nicolasRHUpperEnvelope x * (x ^ (1 / 2 : Real) * Real.log x) < 0) atTop :=
    tendsto_nicolasRHUpperEnvelope_scaled.eventually_lt_const
      (by linarith [robin_zero_constant_le_one_twentieth])
  filter_upwards [hMain, eventually_ge_atTop (4 : Real)] with x hNegative hx
  have hxOne : 1 < x := by linarith
  have hxPos : 0 < x := by linarith
  have hScale : 0 < x ^ (1 / 2 : Real) * Real.log x :=
    mul_pos (Real.rpow_pos_of_pos hxPos _) (Real.log_pos hxOne)
  have hUpper := nicolasK_add_four_div_le_RH_upper_envelope hRH hx
  by_contra hNot
  have hK : 0 <= nicolasK x := le_of_not_gt hNot
  have hFour : 0 <= (4 : Real) / x := by positivity
  have hEnvelope : 0 <= nicolasRHUpperEnvelope x := by linarith
  exact (not_lt_of_ge (mul_nonneg hEnvelope hScale.le)) hNegative

theorem riemannHypothesis_iff_eventually_nicolasK_neg :
    RiemannHypothesis <-> Filter.Eventually (fun x : Real => nicolasK x < 0) atTop := by
  constructor
  . exact eventually_nicolasK_neg_of_RH
  . intro hEvent
    by_contra hNotRH
    choose X hX using eventually_atTop.mp hEvent
    choose x hx hPositive using
      nicolasK_scaled_positive_supply_of_not_RH hNotRH 0 (max X 0)
    have hxNonneg : 0 <= x := le_trans (le_max_right X 0) hx
    have hNegative := hX x (le_trans (le_max_left X 0) hx)
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hxNonneg hNegative.le)) hPositive

theorem riemannHypothesis_iff_eventually_nicolasK_nat_neg :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      nicolasK (N : Real) < 0) atTop := by
  constructor
  . intro hRH
    exact (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : Nat => (N : Real)) atTop atTop).eventually
        (eventually_nicolasK_neg_of_RH hRH)
  . intro hEvent
    by_contra hNotRH
    choose N0 hN0 using eventually_atTop.mp hEvent
    choose N hN hPositive using
      (nicolasK_integer_excursions_of_not_RH hNotRH).1 1 (by norm_num) N0
    have hNonneg : (0 : Real) <= 1 / (N : Real) := by positivity
    linarith [hN0 N hN]

theorem riemannHypothesis_iff_eventually_thetaTailIntegral_neg :
    RiemannHypothesis <-> Filter.Eventually (fun x : Real =>
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Chebyshev.theta t - t) *
          ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) < 0) atTop := by
  simpa only [nicolasK, nicolasThetaError, nicolasTailKernel] using
    riemannHypothesis_iff_eventually_nicolasK_neg

end PrimeFactorOscillations
