/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianLocalizationTail
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianPositiveKernel
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeWaveRecordComparison

/-!
# Localization of the full positive theta probe in the fixed regulator

The entire kernel integral is compared with the actual greedy prime
record. The complementary tail is the fully bounded localization tail.
The large-input theta bound is obtained from the existing unconditional PNT.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Filter

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianThetaProbe_record_localization
    (a tau : Real) (ha : 0 < a) :
    Exists fun X0 : Real => forall X : Real, X0 <= X ->
      (logGaussianThetaProbe X (a ^ 2 * Real.log X) 0).re +
          norm (logGaussianThetaProbe X (a ^ 2 * Real.log X) tau) <=
        2 * (greedyPrimeRegulatorReal (X ^ (1 + a ^ 2 + 2 * a)) +
          Real.log (X ^ (1 + a ^ 2 + 2 * a))) + gaussianLocalizationTail X a := by
  have hPNT := primeClassThetaReal_univ_div_tendsto_one
  choose T hT using Metric.tendsto_atTop.mp hPNT 1 (by norm_num)
  let X0 : Real := max (Real.exp 1) (max 2 T)
  refine Exists.intro X0 ?_
  intro X hScale
  have hExp : Real.exp 1 <= X := (le_max_left _ _).trans hScale
  have hRest : max 2 T <= X := (le_max_right _ _).trans hScale
  have hX2 : 2 <= X := (le_max_left 2 T).trans hRest
  have hXPos : 0 < X := by linarith only [hX2]
  have hLog : 1 <= Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  let V : Real := a ^ 2 * Real.log X
  let h : Real := (a ^ 2 + 2 * a) * Real.log X
  let Y : Real := X ^ (1 + a ^ 2 + 2 * a)
  let A : Real := greedyPrimeRegulatorReal Y + Real.log Y
  have hV : 0 < V := by dsimp only [V]; positivity
  have hh : 0 <= h := by dsimp only [h]; positivity
  have hYeq : Y = X * Real.exp h := by
    dsimp only [Y]
    rw [Real.rpow_def_of_pos hXPos, <- Real.exp_log hXPos, <- Real.exp_add]
    simp only [Real.log_exp]
    congr 1
    dsimp only [h]
    ring
  have hXY : X <= Y := by
    rw [hYeq]
    have hE : 1 <= Real.exp h := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hh
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hE hXPos.le
  have hY2 : 2 <= Y := hX2.trans hXY
  have hYPos : 0 < Y := hXPos.trans_le hXY
  have hA : 0 <= A :=
    add_nonneg (greedyPrimeRegulatorReal_nonneg Y)
      (Real.log_nonneg (by linarith only [hY2]))
  have hRecord : forall t : Real, 0 < t -> t <= Y -> Chebyshev.theta t - t <= A := by
    intro t ht htY
    by_cases ht2 : 2 <= t
    . have hError := primeThetaErrorReal_le_record_log t ht2
      rw [primeClassThetaReal_univ_eq_chebyshev] at hError
      have hMono := greedyPrimeRegulatorReal_mono t Y ht.le htY
      have hLogMono := Real.log_le_log ht htY
      dsimp only [A]
      linarith only [hError, hMono, hLogMono]
    . rw [Chebyshev.theta_eq_zero_of_lt_two (lt_of_not_ge ht2)]
      linarith only [ht, hA]
  have hLarge : forall t : Real, Y <= t -> Chebyshev.theta t - t <= t := by
    intro t ht
    have htPos : 0 < t := hYPos.trans_le ht
    have htT : T <= t := (le_max_right 2 T).trans (hRest.trans (hXY.trans ht))
    have hApprox := hT t htT
    have hAbs : abs (primeClassThetaReal Set.univ t / t - 1) < 1 := by
      simpa only [Real.dist_eq] using hApprox
    rw [primeClassThetaReal_univ_eq_chebyshev] at hAbs
    have hRatio : Chebyshev.theta t / t <= 2 := by
      have := (le_abs_self _).trans hAbs.le
      linarith only [this]
    have hMul := mul_le_mul_of_nonneg_right hRatio htPos.le
    have hCancel : (Chebyshev.theta t / t) * t = Chebyshev.theta t := by
      field_simp [htPos.ne']
    rw [hCancel] at hMul
    linarith only [hMul]
  cases logGaussianThetaProbe_coupled_positive_integral X V tau (by linarith) hV with
  | intro z hz =>
    let F : Real -> Real := fun u =>
      Real.exp u * (Real.log X + abs u) * logGaussianDensity V u
    let W : Real -> Real := fun u =>
      (Chebyshev.theta (X * Real.exp u) - X * Real.exp u) *
        logGaussianPositiveKernel V tau z u
    let M : Real -> Real := fun u =>
      2 * A * logGaussianDensity V u + 2 * X * (Set.Ioi h).indicator F u
    have hF : Integrable F := by
      simpa only [one_mul] using
        logGaussianDensity_weighted_real_tilt_integrable V 1 (Real.log X) hV
    have hW : Integrable W := hz.2.1
    have hM : Integrable M :=
      ((logGaussianDensity_integrable V hV).const_mul (2 * A)).add
        ((hF.indicator measurableSet_Ioi).const_mul (2 * X))
    have hPoint : forall u : Real, W u <= M u := by
      intro u
      let t : Real := X * Real.exp u
      have htPos : 0 < t := mul_pos hXPos (Real.exp_pos _)
      have hK := logGaussianPositiveKernel_bounds V tau u z hV hz.1.le
      have hDensity := (logGaussianDensity_pos V u hV).le
      by_cases hu : h < u
      . have huSet : Membership.mem (Set.Ioi h) u := hu
        have hYt : Y <= t := by
          rw [hYeq]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.le) hXPos.le
        have hE := hLarge t hYt
        have hEK := mul_le_mul_of_nonneg_right hE hK.1
        have hKU := mul_le_mul_of_nonneg_left hK.2 htPos.le
        have hWeight : 1 <= Real.log X + abs u := by
          linarith only [hLog, abs_nonneg u]
        have hTail : 2 * t * logGaussianDensity V u <= 2 * X * F u := by
          have hMul := mul_le_mul_of_nonneg_left hWeight
            (mul_nonneg (mul_nonneg (by positivity : 0 <= 2 * X) (Real.exp_pos u).le) hDensity)
          dsimp only [F, t]
          nlinarith only [hMul]
        dsimp only [W, M]
        rw [Set.indicator_of_mem huSet]
        have hSupply : 0 <= 2 * A * logGaussianDensity V u := by positivity
        change (Chebyshev.theta t - t) * _ <= _
        nlinarith only [hEK, hKU, hTail, hSupply]
      . have huSet : Not (Membership.mem (Set.Ioi h) u) := hu
        have htY : t <= Y := by
          rw [hYeq]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (le_of_not_gt hu)) hXPos.le
        have hE := hRecord t htPos htY
        have hEK := mul_le_mul_of_nonneg_right hE hK.1
        have hKU := mul_le_mul_of_nonneg_left hK.2 hA
        dsimp only [W, M]
        rw [Set.indicator_of_notMem huSet, mul_zero, add_zero]
        change (Chebyshev.theta t - t) * _ <= _
        nlinarith only [hEK, hKU]
    have hIntegral : integral volume W <= integral volume M :=
      integral_mono_ae hW hM (Filter.Eventually.of_forall hPoint)
    have hEvaluation : integral volume M = 2 * A + gaussianLocalizationTail X a := by
      rw [integral_add ((logGaussianDensity_integrable V hV).const_mul (2 * A))
        ((hF.indicator measurableSet_Ioi).const_mul (2 * X)),
        integral_const_mul, integral_const_mul, logGaussianDensity_integral V hV, mul_one]
      rfl
    rw [hEvaluation] at hIntegral
    rw [hz.2.2]
    exact hIntegral

end PrimeFactorOscillations.PrimeClassDeletion
