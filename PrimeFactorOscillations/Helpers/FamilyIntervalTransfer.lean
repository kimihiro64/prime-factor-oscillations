/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPowerPersistence

/-!
# RH transfer through independently bounded correction intervals

Only the width of the correction interval must decay at every power strictly
below the square-root threshold. Its center may be larger and signed.
No local probability or polynomial qualification is assumed by this transfer;
an arithmetic consumer must separately prove its interval bounds.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

theorem riemannHypothesis_iff_eventually_family_interval_le
    (E lower upper : Nat -> Real) (c : Real) (hc : 0 < c)
    (hInterval : Filter.Eventually (fun N : Nat =>
      lower N <= E N - c * nicolasLogMertensOscillation (N : Real) /\
      E N - c * nicolasLogMertensOscillation (N : Real) <= upper N) atTop)
    (hWidth : forall b : Real, 0 < b -> b < 1 / 2 ->
      exists C : Real, 0 < C /\ Filter.Eventually (fun N : Nat =>
        upper N - lower N <= C * (N : Real) ^ (-b)) atTop) :
    RiemannHypothesis <->
      Filter.Eventually (fun N : Nat => E N <= upper N) atTop := by
  constructor
  . intro hRH
    have hNeg := eventually_nicolasLog_nat_lt_neg_div_of_RH hRH 0
    filter_upwards [hNeg, hInterval] with N hN hI
    have hF : nicolasLogMertensOscillation (N : Real) < 0 := by simpa using hN
    have hScaled := mul_neg_of_pos_of_neg hc hF
    linarith only [hI.2, hScaled]
  . intro hEvent
    by_contra hNotRH
    choose b hb hbHalf hWindows using exists_nicolasLog_power_intervals_of_not_RH hNotRH
    choose C hC hBound using hWidth b hb hbHalf
    have hAll := hEvent.and (hInterval.and hBound)
    choose N0 hN0 using eventually_atTop.mp hAll
    have hAmplitude : 0 < (C + 1) / c := div_pos (by linarith) hc
    choose n hn hnSix hF using hWindows 0 ((C + 1) / c) (N0 : Real)
      (by linarith) hAmplitude
    have hn0 : N0 <= n := by exact_mod_cast hn.le
    have hnPos : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
    have hPow : 0 < (n : Real) ^ (-b) := Real.rpow_pos_of_pos hnPos _
    have hPeak := hF (n : Real) le_rfl (by rw [Real.rpow_zero]; linarith)
    have hScaled := mul_lt_mul_of_pos_left hPeak hc
    have hCancel : c * ((C + 1) / c * (n : Real) ^ (-b)) =
        (C + 1) * (n : Real) ^ (-b) := by
      field_simp [hc.ne']
    rw [hCancel] at hScaled
    have hN := hN0 n hn0
    nlinarith only [hN.1, hN.2.1.1, hN.2.2, hScaled, hPow]

theorem riemannHypothesis_iff_eventually_family_interval_lt
    (E lower upper : Nat -> Real) (c : Real) (hc : 0 < c)
    (hInterval : Filter.Eventually (fun N : Nat =>
      lower N <= E N - c * nicolasLogMertensOscillation (N : Real) /\
      E N - c * nicolasLogMertensOscillation (N : Real) <= upper N) atTop)
    (hWidth : forall b : Real, 0 < b -> b < 1 / 2 ->
      exists C : Real, 0 < C /\ Filter.Eventually (fun N : Nat =>
        upper N - lower N <= C * (N : Real) ^ (-b)) atTop) :
    RiemannHypothesis <->
      Filter.Eventually (fun N : Nat => E N < upper N) atTop := by
  constructor
  . intro hRH
    have hNeg := eventually_nicolasLog_nat_lt_neg_div_of_RH hRH 0
    filter_upwards [hNeg, hInterval] with N hN hI
    have hF : nicolasLogMertensOscillation (N : Real) < 0 := by simpa using hN
    have hScaled := mul_neg_of_pos_of_neg hc hF
    linarith only [hI.2, hScaled]
  . intro hEvent
    apply (riemannHypothesis_iff_eventually_family_interval_le
      E lower upper c hc hInterval hWidth).mpr
    filter_upwards [hEvent] with N hN
    exact hN.le

end PrimeFactorOscillations
