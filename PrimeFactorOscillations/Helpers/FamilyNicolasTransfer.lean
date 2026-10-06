/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasCanonicalSign
import PrimeFactorOscillations.Helpers.NicolasNegativeLimit

/-!
# Stable transfer of the Nicolas criterion

The arithmetic error may include a relative error of at most half the positive
signal coefficient and an inverse-cutoff absolute error. No family or gap
conjecture is assumed. Actual family consumers must prove this estimate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

theorem riemannHypothesis_iff_eventually_familyError_le
    (E : Nat -> Real) (c C A : Real) (hc : 0 < c) (hC : 0 <= C)
    (hError : Filter.Eventually (fun N : Nat =>
      abs (E N - c * nicolasLogMertensOscillation (N : Real)) <=
        c / 2 * abs (nicolasLogMertensOscillation (N : Real)) + C / N) atTop) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat => E N <= A / N) atTop := by
  constructor
  . intro hRH
    let D := 2 * (C + abs A + 1) / c
    have hD : 0 < D := by dsimp [D]; positivity
    have hNegative := eventually_nicolasLog_nat_lt_neg_div_of_RH hRH D
    filter_upwards [hNegative, hError, eventually_ge_atTop (1 : Nat)] with N hN hE hOne
    have hn : (0 : Real) < N := by exact_mod_cast hOne
    have hF : nicolasLogMertensOscillation (N : Real) < 0 := by
      have hp : 0 < D / (N : Real) := div_pos hD hn
      rw [neg_div] at hN
      linarith
    rw [abs_of_neg hF] at hE
    have hUpper := (abs_le.mp hE).2
    have hScaled := mul_lt_mul_of_pos_left hN (show 0 < c / 2 by positivity)
    have hCancel : c / 2 * (-D / (N : Real)) = -(C + abs A + 1) / N := by
      dsimp [D]
      field_simp [hc.ne', hn.ne']
      <;> ring
    rw [hCancel] at hScaled
    have hA := neg_abs_le A
    have hADiv := div_le_div_of_nonneg_right hA hn.le
    have hInv : (0 : Real) < 1 / N := one_div_pos.mpr hn
    have hAlgebra : -(C + abs A + 1) / (N : Real) + C / N =
        -abs A / N - 1 / N := by ring
    linarith only [hUpper, hScaled, hADiv, hInv, hAlgebra]
  . intro hEvent
    by_contra hNotRH
    have hAll : Filter.Eventually (fun N : Nat =>
        1 <= N /\ E N <= A / N /\
          abs (E N - c * nicolasLogMertensOscillation (N : Real)) <=
            c / 2 * abs (nicolasLogMertensOscillation (N : Real)) + C / N) atTop := by
      filter_upwards [eventually_ge_atTop (1 : Nat), hEvent, hError] with N hN hE hB
      exact And.intro hN (And.intro hE hB)
    choose N0 hN0 using eventually_atTop.mp hAll
    choose N hN hPeak using nicolasLog_scaled_unbounded_of_not_RH
      hNotRH (2 * (C + abs A + 1) / c) N0
    have hDomain := hN0 N hN
    have hn : (0 : Real) < N := by exact_mod_cast hDomain.1
    have hThreshold : 0 < 2 * (C + abs A + 1) / c := by positivity
    have hF : 0 < nicolasLogMertensOscillation (N : Real) := by
      nlinarith only [hPeak, hThreshold, hn]
    have hBound := hDomain.2.2
    rw [abs_of_pos hF] at hBound
    have hLower := (abs_le.mp hBound).1
    have hWeighted := mul_le_mul_of_nonneg_left hLower hn.le
    have hUpper := mul_le_mul_of_nonneg_left hDomain.2.1 hn.le
    have hCancel : (N : Real) * (C / N) = C := by field_simp
    have hCancelA : (N : Real) * (A / N) = A := by field_simp
    rw [hCancelA] at hUpper
    have hScaled := mul_lt_mul_of_pos_left hPeak (show 0 < c / 2 by positivity)
    have hCancelC : c / 2 * (2 * (C + abs A + 1) / c) = C + abs A + 1 := by
      field_simp [hc.ne']
      <;> ring
    rw [hCancelC] at hScaled
    have hA := le_abs_self A
    nlinarith only [hWeighted, hUpper, hCancel, hScaled, hA]

theorem riemannHypothesis_iff_eventually_familyError_neg
    (E : Nat -> Real) (c C : Real) (hc : 0 < c) (hC : 0 <= C)
    (hError : Filter.Eventually (fun N : Nat =>
      abs (E N - c * nicolasLogMertensOscillation (N : Real)) <=
        c / 2 * abs (nicolasLogMertensOscillation (N : Real)) + C / N) atTop) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat => E N < 0) atTop := by
  constructor
  . intro hRH
    have h := (riemannHypothesis_iff_eventually_familyError_le E c C (-1) hc hC hError).mp hRH
    filter_upwards [h, eventually_ge_atTop (1 : Nat)] with N hN hOne
    have hn : (0 : Real) < N := by exact_mod_cast hOne
    exact hN.trans_lt (div_neg_of_neg_of_pos (by norm_num) hn)
  . intro h
    apply (riemannHypothesis_iff_eventually_familyError_le E c C 0 hc hC hError).mpr
    filter_upwards [h] with N hN
    simpa only [zero_div] using hN.le

end PrimeFactorOscillations
