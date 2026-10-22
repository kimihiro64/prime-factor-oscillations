/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianSignedProbeBound

/-!
# A positive signal at every sufficiently large real scale

All five signed allowances are absorbed using their strict exponent
gaps. The lower bound concerns the actual pair of theta integrals.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter

theorem gaussian_power_ratio_tendsto
    (a B : Real) (hGap : a < B) :
    Tendsto (fun X : Real => X ^ a / X ^ B) atTop (nhds 0) := by
  have h := (tendsto_rpow_atTop (sub_pos.mpr hGap)).const_div_atTop (1 : Real)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with X hX
  rw [Real.rpow_sub hX]
  field_simp

theorem gaussian_power_log_ratio_tendsto
    (a B : Real) (hGap : a < B) :
    Tendsto (fun X : Real => X ^ a * Real.log X / X ^ B) atTop (nhds 0) := by
  have h : Tendsto (fun X : Real => Real.log X / X ^ (B - a)) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (sub_pos.mpr hGap)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with X hX
  rw [Real.rpow_sub hX]
  field_simp

theorem logGaussianThetaProbe_eventual_positive_signal
    (c tau : Real) (hc : 0 < c) (hcOne : c < 1) (w : ZetaDistinctZero)
    (hUnique : forall z : ZetaDistinctZero, Not (z = w) ->
      gaussianZeroExponent c z.val.re z.val.im tau <
        gaussianZeroExponent c w.val.re w.val.im tau)
    (hEnvelope : gaussianZetaEnvelope c 0 <
      gaussianZeroExponent c w.val.re w.val.im tau)
    (hPrimePower : 1 / 2 + c / 8 <
      gaussianZeroExponent c w.val.re w.val.im tau) :
    Exists fun X0 : Real => forall X : Real, X0 <= X ->
      (gaussianZetaAmplitude w / 2) *
          X ^ (gaussianZeroExponent c w.val.re w.val.im tau) <=
        (logGaussianThetaProbe X (c * Real.log X) 0).re +
          norm (logGaussianThetaProbe X (c * Real.log X) tau) := by
  cases logGaussianThetaProbe_coupled_signed_lower_bound c tau hc w hUnique with
  | intro delta hd =>
    cases hd.2.2 with
    | intro C1 hC1 =>
      cases hC1.2 with
      | intro C0 hC0 =>
        let B : Real := gaussianZeroExponent c w.val.re w.val.im tau
        let P : Real := 4 * (2 + c / 2 + 2 * c / Real.pi)
        let K : Real := logGaussianExplicitErrorConstant tau + logGaussianExplicitErrorConstant 0
        let A : Real := 2 * abs (Real.log (2 * Real.pi))
        let E : Real -> Real := fun X =>
          C1 * X ^ (B - delta) + C0 * X ^ (gaussianZetaEnvelope c 0) +
            A + K * X ^ (-1 + c / 2) + P * X ^ (1 / 2 + c / 8) * Real.log X
        have hB : 0 < B := by
          change 1 / 2 + c / 8 < B at hPrimePower
          linarith
        have hTail : Tendsto (fun X : Real => C1 * (X ^ (B - delta) / X ^ B))
            atTop (nhds 0) := by
          simpa only [mul_zero] using
            (gaussian_power_ratio_tendsto (B - delta) B (by linarith only [hd.1])).const_mul C1
        have hZero : Tendsto
            (fun X : Real => C0 * (X ^ (gaussianZetaEnvelope c 0) / X ^ B))
            atTop (nhds 0) := by
          simpa only [mul_zero] using
            (gaussian_power_ratio_tendsto (gaussianZetaEnvelope c 0) B hEnvelope).const_mul C0
        have hConstant : Tendsto (fun X : Real => A / X ^ B) atTop (nhds 0) :=
          (tendsto_rpow_atTop hB).const_div_atTop A
        have hPhysical : Tendsto (fun X : Real => K * (X ^ (-1 + c / 2) / X ^ B))
            atTop (nhds 0) := by
          have hGap : -1 + c / 2 < B := by linarith
          simpa only [mul_zero] using
            (gaussian_power_ratio_tendsto (-1 + c / 2) B hGap).const_mul K
        have hLog : Tendsto
            (fun X : Real => P * (X ^ (1 / 2 + c / 8) * Real.log X / X ^ B))
            atTop (nhds 0) := by
          simpa only [mul_zero] using
            (gaussian_power_log_ratio_tendsto (1 / 2 + c / 8) B hPrimePower).const_mul P
        have hSum := (((hTail.add hZero).add hConstant).add hPhysical).add hLog
        simp only [add_zero] at hSum
        have hError : Tendsto (fun X : Real => E X / X ^ B) atTop (nhds 0) := by
          apply hSum.congr'
          filter_upwards [] with X
          dsimp only [E]
          ring
        have hAmplitude : 0 < gaussianZetaAmplitude w / 2 := by
          exact div_pos (gaussianZetaAmplitude_pos w) (by norm_num)
        choose X2 hX2 using Metric.tendsto_atTop.mp hError
          (gaussianZetaAmplitude w / 2) hAmplitude
        refine Exists.intro (max (Real.exp (1 / c)) (max (Real.exp 1) X2)) ?_
        intro X hX0
        have hBase := (le_max_left (Real.exp (1 / c)) (max (Real.exp 1) X2)).trans hX0
        have hRest := (le_max_right (Real.exp (1 / c)) (max (Real.exp 1) X2)).trans hX0
        have hExp := (le_max_left (Real.exp 1) X2).trans hRest
        have hX2' := (le_max_right (Real.exp 1) X2).trans hRest
        have hXPos : 0 < X := (Real.exp_pos (1 / c)).trans_le hBase
        have hPower : 0 < X ^ B := Real.rpow_pos_of_pos hXPos B
        have hSmall := hX2 X hX2'
        have hAbs : abs (E X / X ^ B) < gaussianZetaAmplitude w / 2 := by
          simpa only [Real.dist_eq, sub_zero] using hSmall
        have hRatio : E X / X ^ B <= gaussianZetaAmplitude w / 2 :=
          (le_abs_self _).trans hAbs.le
        have hAbsorb : E X <= (gaussianZetaAmplitude w / 2) * X ^ B := by
          have hMul := mul_le_mul_of_nonneg_right hRatio hPower.le
          have hCancel : (E X / X ^ B) * X ^ B = E X := by
            field_simp [hPower.ne']
          rwa [hCancel] at hMul
        have hSigned := hC0.2 X hBase hExp
        change _ <= (logGaussianThetaProbe X (c * Real.log X) 0).re +
          norm (logGaussianThetaProbe X (c * Real.log X) tau) at hSigned
        have hRearrange :
            gaussianZetaAmplitude w * X ^ B - E X <=
              (logGaussianThetaProbe X (c * Real.log X) 0).re +
                norm (logGaussianThetaProbe X (c * Real.log X) tau) := by
          dsimp only [E, P, K, A, B]
          linarith only [hSigned]
        change (gaussianZetaAmplitude w / 2) * X ^ B <= _
        linarith only [hAbsorb, hRearrange]

end PrimeFactorOscillations.PrimeClassDeletion
