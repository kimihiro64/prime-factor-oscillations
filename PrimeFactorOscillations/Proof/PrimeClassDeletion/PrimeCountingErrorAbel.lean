/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.GapFrequencyCoverage
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassAbel

/-!
# The complete signed prime-count error identity

The single-log reference Li_1 is distinct from the existing double-log
gap-count reference Li_2. Both lower endpoints and the full theta error
remain in the exact partial-summation consumer.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def primeLogarithmicIntegral (x : Real) : Real :=
  intervalIntegral (fun t : Real => 1 / Real.log t) 2 x volume

private theorem logInversePow_intervalIntegrable (k : Nat) (x : Real) (hx : 2 <= x) :
    IntervalIntegrable (fun t : Real => 1 / (Real.log t) ^ k) volume 2 x := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hx]
  apply continuousOn_const.div
  . exact (Real.continuousOn_log.mono (by
      intro t ht
      exact ne_of_gt (by linarith only [ht.1] : 0 < t))).pow k
  . intro t ht
    exact pow_ne_zero k (Real.log_pos (by linarith only [ht.1] : 1 < t)).ne'

theorem primeLogarithmicIntegral_eq_boundary_add_double_log_integral
    (x : Real) (hx : 2 <= x) :
    primeLogarithmicIntegral x =
      x / Real.log x - 2 / Real.log 2 + logarithmicIntegralTwo x := by
  have hI1 : IntervalIntegrable (fun t : Real => 1 / Real.log t) volume 2 x := by
    simpa only [pow_one] using logInversePow_intervalIntegrable 1 x hx
  have hI2 := logInversePow_intervalIntegrable 2 x hx
  have hDeriv : forall t : Real, Membership.mem (Set.uIcc (2 : Real) x) t ->
      HasDerivAt (fun y : Real => y / Real.log y)
        (1 / Real.log t - 1 / (Real.log t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith only [ht.1]
    have hL : 0 < Real.log t := Real.log_pos (by linarith only [ht.1])
    have h := (hasDerivAt_id t).div (Real.hasDerivAt_log ht0.ne') hL.ne'
    change HasDerivAt (fun y : Real => y / Real.log y)
      ((1 * Real.log t - t * Inv.inv t) / (Real.log t) ^ 2) t at h
    convert h using 1; field_simp [hL.ne', ht0.ne']
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv (hI1.sub hI2)
  rw [intervalIntegral.integral_sub hI1 hI2] at h
  change primeLogarithmicIntegral x - logarithmicIntegralTwo x =
    x / Real.log x - 2 / Real.log 2 at h
  linarith only [h]

theorem primeClassCount_error_abel (P : Set Nat) (x : Real) (hx : 2 <= x) :
    ((primeClassPrefix P (Nat.floor x)).card : Real) - primeLogarithmicIntegral x =
      2 / Real.log 2 + (primeClassThetaReal P x - x) / Real.log x +
        intervalIntegral (fun t =>
          (primeClassThetaReal P t - t) / (t * (Real.log t) ^ 2)) 2 x volume := by
  have hITheta := primeClassAbel_intervalIntegrable P x hx
  have hI2 := logInversePow_intervalIntegrable 2 x hx
  have hError : intervalIntegral (fun t =>
        (primeClassThetaReal P t - t) / (t * (Real.log t) ^ 2)) 2 x volume =
      intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
        2 x volume - logarithmicIntegralTwo x := by
    calc
      _ = intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2) 2 x volume := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        have ht0 : 0 < t := by linarith only [ht.1]
        field_simp [ht0.ne']
      _ = _ := by
        rw [intervalIntegral.integral_sub hITheta hI2]
        rfl
  rw [primeClassCount_abel P x hx,
    primeLogarithmicIntegral_eq_boundary_add_double_log_integral x hx, hError]
  ring

theorem primeCounting_error_abel (x : Real) (hx : 2 <= x) :
    (Nat.primeCounting (Nat.floor x) : Real) - primeLogarithmicIntegral x =
      2 / Real.log 2 + (Chebyshev.theta x - x) / Real.log x +
        intervalIntegral (fun t =>
          (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) 2 x volume := by
  simpa only [primeClassPrefix_univ_card_eq_primeCounting,
    primeClassThetaReal_univ_eq_chebyshev] using primeClassCount_error_abel Set.univ x hx

end PrimeFactorOscillations.PrimeClassDeletion
