/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasNegativeLimit
import PrimeFactorOscillations.Helpers.PrimeProfileCanonicalLinearization

/-!
# Simultaneous RH comparison across compact rank bands

The actual negative Nicolas margin dominates both terms of the proved
uniform linearization error. All ranks in the fixed positive compact band
are handled simultaneously after one cutoff.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

theorem eventually_densityRatio_thetaClock_lt_reference_uniform_of_RH
    (hRH : RiemannHypothesis) (a b : Real) (ha : 0 < a) (hab : a <= b) :
    Filter.Eventually (fun x : Real =>
      let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
      1 < Chebyshev.theta x /\ 2 <= L /\
      forall r : Nat, a <= (r : Real) / L -> (r : Real) / L <= b ->
        0 < (PrimeFactorUnimodality.weightEsymm
          (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) /\
        0 < Nat.factorialConvolution primeProfileRealCoefficient r L /\
        (PrimeFactorUnimodality.densityRatio
          (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) <
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
            Nat.factorialConvolution primeProfileRealCoefficient r L) atTop := by
  have hb : 0 < b := ha.trans_le hab
  choose r0 K hr0 hK hApprox using
    exists_eventually_densityRatio_real_thetaClock_linearization b hb
  let C : Real := 2 * K / a ^ 2 + 1
  have hCPos : 0 < C := by dsimp [C]; positivity
  have hCIdentity : a ^ 2 * C = 2 * K + a ^ 2 := by
    dsimp [C]
    field_simp [ha.ne']
    <;> ring
  have hCStrong : 2 * K < a ^ 2 * C := by nlinarith [sq_pos_of_pos ha]
  have hTheta : Tendsto Chebyshev.theta atTop atTop :=
    primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id
  have hClock : Tendsto (fun x : Real => Real.eulerMascheroniConstant +
      Real.log (Real.log (Chebyshev.theta x))) atTop atTop :=
    tendsto_const_nhds.add_atTop
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hTheta))
  filter_upwards [hApprox, eventually_nicolasLog_lt_neg_div_of_RH hRH C,
    hClock.eventually_ge_atTop (((r0 : Real) + 2 * K + 1) / a),
    eventually_ge_atTop (2 : Real)] with x hApproxX hMargin hLarge hxTwo
  let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
  let F := nicolasLogMertensOscillation x
  have hLTwo : 2 <= L := hApproxX.2.1
  have hLPos : 0 < L := by linarith
  have hxPos : 0 < x := by linarith
  change ((r0 : Real) + 2 * K + 1) / a <= L at hLarge
  change F < -C / x at hMargin
  rw [neg_div] at hMargin
  refine And.intro hApproxX.1 (And.intro hLTwo ?_)
  intro r hLow hHigh
  have hRankLower : a * L <= (r : Real) := by
    calc
      a * L <= ((r : Real) / L) * L :=
        _root_.mul_le_mul_of_nonneg_right hLow hLPos.le
      _ = (r : Real) := by field_simp [hLPos.ne']
  have hRankLarge : (r0 : Real) + 2 * K + 1 <= (r : Real) := by
    calc
      (r0 : Real) + 2 * K + 1 = a * (((r0 : Real) + 2 * K + 1) / a) := by
        field_simp [ha.ne']
      _ <= a * L := _root_.mul_le_mul_of_nonneg_left hLarge ha.le
      _ <= (r : Real) := hRankLower
  have hRank0 : r0 <= r := by
    have hReal : (r0 : Real) <= (r : Real) := by linarith
    exact_mod_cast hReal
  have hrReal : (0 : Real) < r := by exact_mod_cast hr0.trans_le hRank0
  have hReserve : 2 * K <= (r : Real) := by
    have hr0Nonneg : (0 : Real) <= r0 := Nat.cast_nonneg r0
    linarith
  have hRank := hApproxX.2.2 r hRank0 hHigh
  let D := (PrimeFactorUnimodality.densityRatio
    (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real)
  let R := Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
    Nat.factorialConvolution primeProfileRealCoefficient r L
  have hError : abs (D - R - ((r : Real) / L ^ 2) * F) <=
      K * (abs F / L ^ 2 + 1 / ((r : Real) * x)) := hRank.2.2
  have hCoverPos : 0 < C / x := div_pos hCPos hxPos
  have hFNeg : F < 0 := by linarith
  rw [abs_of_neg hFNeg] at hError
  have hUpper := (abs_le.mp hError).2
  have hBasic : D - R <= (((r : Real) - K) / L ^ 2) * F +
      K / ((r : Real) * x) := by
    have hExpand : K * (-F / L ^ 2 + 1 / ((r : Real) * x)) +
        ((r : Real) / L ^ 2) * F =
      (((r : Real) - K) / L ^ 2) * F + K / ((r : Real) * x) := by ring
    rw [<- hExpand]
    linarith only [hUpper]
  have hSquare : a ^ 2 <= ((r : Real) / L) ^ 2 := by gcongr
  have hWeightedSquare := _root_.mul_le_mul_of_nonneg_right hSquare hCPos.le
  have hNumerator : K < (((r : Real) / L) ^ 2 * C) / 2 := by nlinarith
  have hGain : K / ((r : Real) * x) <
      ((r : Real) / (2 * L ^ 2)) * (C / x) := by
    calc
      K / ((r : Real) * x) <
          ((((r : Real) / L) ^ 2 * C) / 2) / ((r : Real) * x) := by gcongr
      _ = ((r : Real) / (2 * L ^ 2)) * (C / x) := by
        field_simp [hrReal.ne', hxPos.ne', hLPos.ne']
        <;> ring
  have hCoeff : (r : Real) / (2 * L ^ 2) <= ((r : Real) - K) / L ^ 2 := by
    calc
      (r : Real) / (2 * L ^ 2) = ((r : Real) / 2) / L ^ 2 := by ring
      _ <= ((r : Real) - K) / L ^ 2 :=
        _root_.div_le_div_of_nonneg_right (by linarith) (sq_nonneg L)
  have hCoeffPos : 0 < ((r : Real) - K) / L ^ 2 :=
    div_pos (by linarith) (sq_pos_of_pos hLPos)
  have hGainFull := hGain.trans_le
    (_root_.mul_le_mul_of_nonneg_right hCoeff hCoverPos.le)
  have hSigned := mul_lt_mul_of_pos_left hMargin hCoeffPos
  rw [mul_neg] at hSigned
  refine And.intro hRank.1 (And.intro hRank.2.1 ?_)
  change D < R
  linarith only [hBasic, hGainFull, hSigned]

end PrimeFactorOscillations
