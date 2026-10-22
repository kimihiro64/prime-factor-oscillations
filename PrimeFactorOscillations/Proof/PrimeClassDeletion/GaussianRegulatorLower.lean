/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianRecordLocalization

/-!
# A power lower bound for the fixed greedy regulator

The positive signal is localized, and both the complete physical tail
and the record overshoot are absorbed. The conclusion holds at every
sufficiently large real scale with an explicit positive residue constant.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem greedyPrimeRegulatorReal_gaussian_power_lower
    (a tau : Real) (ha : 0 < a) (haSmall : a < 1 / 4) (w : ZetaDistinctZero)
    (hUnique : forall z : ZetaDistinctZero, Not (z = w) ->
      gaussianZeroExponent (a ^ 2) z.val.re z.val.im tau <
        gaussianZeroExponent (a ^ 2) w.val.re w.val.im tau)
    (hEnvelope : gaussianZetaEnvelope (a ^ 2) 0 <
      gaussianZeroExponent (a ^ 2) w.val.re w.val.im tau)
    (hPrimePower : 1 / 2 + a ^ 2 / 8 <
      gaussianZeroExponent (a ^ 2) w.val.re w.val.im tau) :
    Exists fun X0 : Real => forall X : Real, X0 <= X ->
      (gaussianZetaAmplitude w / 8) *
          X ^ (gaussianZeroExponent (a ^ 2) w.val.re w.val.im tau) <=
        greedyPrimeRegulatorReal (X ^ (1 + a ^ 2 + 2 * a)) := by
  let B : Real := gaussianZeroExponent (a ^ 2) w.val.re w.val.im tau
  let s : Real := 1 + a ^ 2 + 2 * a
  have hB : 0 < B := by
    change 1 / 2 + a ^ 2 / 8 < B at hPrimePower
    nlinarith only [hPrimePower, sq_nonneg a]
  have hc : 0 < a ^ 2 := sq_pos_of_pos ha
  have hcOne : a ^ 2 < 1 := by nlinarith only [ha, haSmall]
  choose T1 hT1 using logGaussianThetaProbe_eventual_positive_signal
    (a ^ 2) tau hc hcOne w hUnique hEnvelope hPrimePower
  choose T2 hT2 using logGaussianThetaProbe_record_localization a tau ha
  have hLog : Tendsto (fun X : Real => Real.log X / X ^ B) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using gaussian_power_log_ratio_tendsto 0 B hB
  have hTail := gaussianLocalizationTail_div_power_tendsto a B ha haSmall hB
  have hLogScaled := hLog.const_mul (2 * s)
  simp only [mul_zero] at hLogScaled
  have hCombined := hLogScaled.add hTail
  simp only [add_zero] at hCombined
  have hError : Tendsto
      (fun X : Real =>
        (2 * Real.log (X ^ s) + gaussianLocalizationTail X a) / X ^ B)
      atTop (nhds 0) := by
    apply hCombined.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with X hX
    simp only [Real.rpow_def_of_pos hX, Real.log_exp]
    ring
  have hAmp : 0 < gaussianZetaAmplitude w / 4 :=
    div_pos (gaussianZetaAmplitude_pos w) (by norm_num)
  choose T3 hT3 using Metric.tendsto_atTop.mp hError
    (gaussianZetaAmplitude w / 4) hAmp
  refine Exists.intro (max (max (Real.exp 1) T1) (max T2 T3)) ?_
  intro X hX0
  have hFirst := (le_max_left (max (Real.exp 1) T1) (max T2 T3)).trans hX0
  have hSecond := (le_max_right (max (Real.exp 1) T1) (max T2 T3)).trans hX0
  have hExp := (le_max_left (Real.exp 1) T1).trans hFirst
  have hPositive := hT1 X ((le_max_right (Real.exp 1) T1).trans hFirst)
  have hLocal := hT2 X ((le_max_left T2 T3).trans hSecond)
  have hApprox := hT3 X ((le_max_right T2 T3).trans hSecond)
  have hX : 0 < X := (Real.exp_pos 1).trans_le hExp
  have hPower : 0 < X ^ B := Real.rpow_pos_of_pos hX B
  have hAbs :
      abs ((2 * Real.log (X ^ s) + gaussianLocalizationTail X a) / X ^ B) <
        gaussianZetaAmplitude w / 4 := by
    simpa only [Real.dist_eq, sub_zero] using hApprox
  have hRatio :
      (2 * Real.log (X ^ s) + gaussianLocalizationTail X a) / X ^ B <=
        gaussianZetaAmplitude w / 4 := (le_abs_self _).trans hAbs.le
  have hMul := mul_le_mul_of_nonneg_right hRatio hPower.le
  have hCancel :
      ((2 * Real.log (X ^ s) + gaussianLocalizationTail X a) / X ^ B) * X ^ B =
        2 * Real.log (X ^ s) + gaussianLocalizationTail X a := by
    field_simp [hPower.ne']
  rw [hCancel] at hMul
  change (gaussianZetaAmplitude w / 2) * X ^ B <= _ at hPositive
  change _ <= 2 * (greedyPrimeRegulatorReal (X ^ s) + Real.log (X ^ s)) +
    gaussianLocalizationTail X a at hLocal
  change (gaussianZetaAmplitude w / 8) * X ^ B <= _
  linarith only [hPositive, hLocal, hMul]

end PrimeFactorOscillations.PrimeClassDeletion
