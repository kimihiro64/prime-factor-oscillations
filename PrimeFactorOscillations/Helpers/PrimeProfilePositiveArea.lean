/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPositiveArea
import PrimeFactorOscillations.Helpers.PrimeProfilePowerExcursions

/-!
# Positive-area RH criterion for the actual moving-rank residual

The prescribed floor rank retains positive actual and reference denominators.
Its normalized residual differs from the Nicolas logarithm by at most
(C/L)|F| + C/x. The positive areas compare in both directions with bounded
additive losses, giving the actual density-residual area criterion for RH.
This result is separate from the localized ascent and separated-reversal
count criteria; those require their own finite sampling and interval inputs.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter MeasureTheory Set Robin1984

def primeProfileThetaClock (x : Real) : Real :=
  Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))

def primeProfileMovingRank (alpha x : Real) : Nat :=
  Nat.floor (alpha * primeProfileThetaClock x)

def primeProfileMovingResidual (alpha x : Real) : Real :=
  let L := primeProfileThetaClock x
  let r := primeProfileMovingRank alpha x
  L ^ (2 : Nat) / (r : Real) *
    ((PrimeFactorUnimodality.densityRatio
      (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) -
      Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
        Nat.factorialConvolution primeProfileRealCoefficient r L)

theorem exists_eventually_primeProfileMovingResidual_error
    (alpha : Real) (ha : 0 < alpha) :
    exists C : Real, 0 <= C /\ Filter.Eventually (fun x : Real =>
      1 < Chebyshev.theta x /\ 2 <= primeProfileThetaClock x /\
      0 < primeProfileMovingRank alpha x /\
      0 < (PrimeFactorUnimodality.weightEsymm
        (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1))
          (primeProfileMovingRank alpha x) : Real) /\
      0 < Nat.factorialConvolution primeProfileRealCoefficient
        (primeProfileMovingRank alpha x) (primeProfileThetaClock x) /\
      abs (primeProfileMovingResidual alpha x - nicolasLogMertensOscillation x) <=
        (C / primeProfileThetaClock x) * abs (nicolasLogMertensOscillation x) + C / x)
      atTop := by
  choose r0 K hr0 hK hApprox using
    exists_eventually_densityRatio_real_thetaClock_linearization (alpha + 1) (by linarith)
  have hTheta : Tendsto Chebyshev.theta atTop atTop :=
    primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id
  have hClock : Tendsto primeProfileThetaClock atTop atTop :=
    tendsto_const_nhds.add_atTop
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hTheta))
  let C : Real := 2 * K / alpha + 4 * K / alpha ^ (2 : Nat)
  have hC : 0 <= C := by dsimp [C]; positivity
  refine Exists.intro C (And.intro hC ?_)
  filter_upwards [hApprox, hClock.eventually_ge_atTop (((r0 : Real) + 2) / alpha),
    eventually_gt_atTop (1 : Real)] with x hApproxX hLarge hx
  let L : Real := primeProfileThetaClock x
  let r : Nat := primeProfileMovingRank alpha x
  let F : Real := nicolasLogMertensOscillation x
  let D : Real := (PrimeFactorUnimodality.densityRatio
    (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) -
    Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
      Nat.factorialConvolution primeProfileRealCoefficient r L
  have hLTwo : 2 <= L := hApproxX.2.1
  have hLPos : 0 < L := by linarith
  have hxPos : 0 < x := by linarith
  have hRankLarge : (r0 : Real) + 2 <= alpha * L := by
    calc
      _ = alpha * (((r0 : Real) + 2) / alpha) := by field_simp [ha.ne']
      _ <= alpha * L := mul_le_mul_of_nonneg_left hLarge ha.le
  have hAlphaL : 2 <= alpha * L := by
    linarith [show (0 : Real) <= r0 from Nat.cast_nonneg r0]
  have hUpper : (r : Real) <= alpha * L := Nat.floor_le (by positivity)
  have hStrictLower : alpha * L < (r : Real) + 1 := Nat.lt_floor_add_one _
  have hRankLower : (alpha / 2) * L <= (r : Real) := by
    nlinarith only [hStrictLower, hAlphaL]
  have hr0r : r0 <= r := Nat.le_floor (by linarith only [hRankLarge])
  have hr : 0 < r := hr0.trans_le hr0r
  have hrPos : (0 : Real) < r := by exact_mod_cast hr
  have hHigh : (r : Real) / L <= alpha + 1 := by
    calc
      _ <= (alpha * L) / L := div_le_div_of_nonneg_right hUpper hLPos.le
      _ = alpha := by field_simp [hLPos.ne']
      _ <= _ := by linarith
  have hApproxR := hApproxX.2.2 r hr0r hHigh
  have hError : abs (D - ((r : Real) / L ^ (2 : Nat)) * F) <=
      K * (abs F / L ^ (2 : Nat) + 1 / ((r : Real) * x)) := hApproxR.2.2
  have hScale : 0 <= L ^ (2 : Nat) / (r : Real) := by positivity
  have hIdentity : primeProfileMovingResidual alpha x - F =
      (L ^ (2 : Nat) / (r : Real)) * (D - ((r : Real) / L ^ (2 : Nat)) * F) := by
    change L ^ (2 : Nat) / (r : Real) * D - F = _
    field_simp [hLPos.ne', hrPos.ne']
  have hNormalized :
      abs (primeProfileMovingResidual alpha x - F) <=
        (K / (r : Real)) * abs F + K * L ^ (2 : Nat) / ((r : Real) ^ (2 : Nat) * x) := by
    rw [hIdentity, abs_mul, abs_of_nonneg hScale]
    have h := mul_le_mul_of_nonneg_left hError hScale
    convert h using 1
    field_simp [hLPos.ne', hrPos.ne', hxPos.ne']
  have hInverse : 1 / (r : Real) <= 2 / (alpha * L) := by
    have h := one_div_le_one_div_of_le (by positivity : 0 < (alpha / 2) * L) hRankLower
    convert h using 1
    field_simp [ha.ne', hLPos.ne']
  have hFirst : K / (r : Real) <= (2 * K / alpha) / L := by
    have h := mul_le_mul_of_nonneg_left hInverse hK
    convert h using 1 <;> ring
  have hRatio : L / (r : Real) <= 2 / alpha := by
    have h := mul_le_mul_of_nonneg_left hInverse hLPos.le
    convert h using 1
    . ring
    . field_simp [ha.ne', hLPos.ne']
  have hSquared : (L / (r : Real)) ^ (2 : Nat) <= (2 / alpha) ^ (2 : Nat) := by
    nlinarith only [hRatio, show 0 <= L / (r : Real) by positivity,
      show 0 <= 2 / alpha by positivity]
  have hSecond :
      K * L ^ (2 : Nat) / ((r : Real) ^ (2 : Nat) * x) <=
        (4 * K / alpha ^ (2 : Nat)) / x := by
    have h := mul_le_mul_of_nonneg_left hSquared (div_nonneg hK hxPos.le)
    convert h using 1 <;> ring
  have hC1 : 2 * K / alpha <= C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  have hC2 : 4 * K / alpha ^ (2 : Nat) <= C := by
    dsimp [C]
    exact le_add_of_nonneg_left (by positivity)
  refine And.intro hApproxX.1 (And.intro hLTwo
    (And.intro hr (And.intro hApproxR.1 (And.intro hApproxR.2.1 ?_))))
  calc
    _ <= (K / (r : Real)) * abs F +
        K * L ^ (2 : Nat) / ((r : Real) ^ (2 : Nat) * x) := hNormalized
    _ <= ((2 * K / alpha) / L) * abs F +
        (4 * K / alpha ^ (2 : Nat)) / x :=
      add_le_add (mul_le_mul_of_nonneg_right hFirst (abs_nonneg F)) hSecond
    _ <= (C / L) * abs F + C / x :=
      add_le_add (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hC1 hLPos.le) (abs_nonneg F))
        (div_le_div_of_nonneg_right hC2 hxPos.le)

def primeProfilePositiveArea (alpha x : Real) : ENNReal :=
  lintegral (volume.restrict (Icc x (2 * x)))
    (fun y : Real => ENNReal.ofReal (primeProfileMovingResidual alpha y))

theorem exists_eventually_primeProfileMovingResidual_positive_parts
    (alpha : Real) (ha : 0 < alpha) :
    exists C : Real, 0 <= C /\ Filter.Eventually (fun x : Real =>
      max (primeProfileMovingResidual alpha x) 0 <=
        (3 / 2 : Real) * max (nicolasLogMertensOscillation x) 0 + C / x /\
      max (nicolasLogMertensOscillation x) 0 <=
        2 * max (primeProfileMovingResidual alpha x) 0 + 2 * C / x) atTop := by
  choose C hC hError using exists_eventually_primeProfileMovingResidual_error alpha ha
  have hTheta : Tendsto Chebyshev.theta atTop atTop :=
    primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id
  have hClock : Tendsto primeProfileThetaClock atTop atTop :=
    tendsto_const_nhds.add_atTop
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hTheta))
  refine Exists.intro C (And.intro hC ?_)
  filter_upwards [hError, hClock.eventually_ge_atTop (2 * C),
    eventually_gt_atTop (1 : Real)] with x hErrorX hLarge hx
  let F : Real := nicolasLogMertensOscillation x
  let S : Real := primeProfileMovingResidual alpha x
  have hLPos : 0 < primeProfileThetaClock x := by linarith [hErrorX.2.1]
  have hxPos : 0 < x := by linarith
  have hRatio : C / primeProfileThetaClock x <= (1 / 2 : Real) := by
    calc
      _ <= (primeProfileThetaClock x / 2) / primeProfileThetaClock x :=
        div_le_div_of_nonneg_right (by linarith) hLPos.le
      _ = _ := by field_simp [hLPos.ne']
  have hRaw : abs (S - F) <= (1 / 2 : Real) * abs F + C / x := by
    apply hErrorX.2.2.2.2.2.trans
    exact add_le_add (mul_le_mul_of_nonneg_right hRatio (abs_nonneg F)) le_rfl
  have hDelta : 0 <= C / x := div_nonneg hC hxPos.le
  have hUpper := (abs_le.mp hRaw).2
  have hLower := (abs_le.mp hRaw).1
  change max S 0 <= (3 / 2 : Real) * max F 0 + C / x /\
    max F 0 <= 2 * max S 0 + 2 * C / x
  constructor
  . apply max_le
    . rcases le_total 0 F with hF | hF
      . rw [abs_of_nonneg hF] at hUpper
        rw [max_eq_left hF]
        linarith only [hUpper]
      . rw [abs_of_nonpos hF] at hUpper
        rw [max_eq_right hF]
        linarith only [hUpper, hF]
    . positivity
  . by_cases hF : 0 <= F
    . rw [abs_of_nonneg hF] at hLower
      rw [max_eq_left hF]
      have hS := le_max_left S 0
      rw [show 2 * C / x = 2 * (C / x) by ring]
      linarith only [hLower, hS]
    . rw [max_eq_right (le_of_not_ge hF)]
      have hS := le_max_right S 0
      positivity

theorem exists_eventually_primeProfilePositiveArea_compare
    (alpha : Real) (ha : 0 < alpha) :
    exists C : Real, 0 <= C /\ Filter.Eventually (fun x : Real =>
      primeProfilePositiveArea alpha x <=
        ENNReal.ofReal (3 / 2 : Real) * nicolasPositiveArea x + ENNReal.ofReal C /\
      nicolasPositiveArea x <=
        ENNReal.ofReal (2 : Real) * primeProfilePositiveArea alpha x +
          ENNReal.ofReal (2 * C)) atTop := by
  have hMax (t : Real) : ENNReal.ofReal (max t 0) = ENNReal.ofReal t := by
    rcases le_total 0 t with ht | ht
    . rw [max_eq_left ht]
    . rw [max_eq_right ht, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero.mpr ht]
  have compare (f g : Real -> Real) (c e x : Real)
      (hc : 0 <= c) (he : 0 <= e)
      (hPoint : forall y : Real, x <= y -> y <= 2 * x ->
        max (f y) 0 <= c * max (g y) 0 + e) :
      lintegral (volume.restrict (Icc x (2 * x))) (fun y => ENNReal.ofReal (f y)) <=
        ENNReal.ofReal c *
          lintegral (volume.restrict (Icc x (2 * x))) (fun y => ENNReal.ofReal (g y)) +
        ENNReal.ofReal (e * x) := by
    have h : Filter.Eventually (fun y : Real =>
        ENNReal.ofReal (f y) <= ENNReal.ofReal c * ENNReal.ofReal (g y) + ENNReal.ofReal e)
        (ae (volume.restrict (Icc x (2 * x)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      calc
        _ <= ENNReal.ofReal (c * max (g y) 0 + e) :=
          ENNReal.ofReal_le_ofReal ((le_max_left (f y) 0).trans (hPoint y hy.1 hy.2))
        _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) he, ENNReal.ofReal_mul hc, hMax]
    have hi := lintegral_mono_ae h
    rw [lintegral_add_right _ measurable_const,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
      show 2 * x - x = x by ring, <- ENNReal.ofReal_mul he] at hi
    exact hi
  choose C hC hEvent using exists_eventually_primeProfileMovingResidual_positive_parts alpha ha
  choose X hX using eventually_atTop.mp hEvent
  refine Exists.intro C (And.intro hC ?_)
  filter_upwards [eventually_ge_atTop X, eventually_gt_atTop (1 : Real)] with x hxX hx
  have hxPos : 0 < x := by linarith
  have hCancel : (C / x) * x = C := by field_simp [hxPos.ne']
  have hCancelTwo : ((2 * C) / x) * x = 2 * C := by field_simp [hxPos.ne']
  constructor
  . have h := compare (primeProfileMovingResidual alpha) nicolasLogMertensOscillation
      (3 / 2) (C / x) x (by norm_num) (div_nonneg hC hxPos.le) (by
        intro y hyl _hyu
        have hp := (hX y (hxX.trans hyl)).1
        have hdiv := div_le_div_of_nonneg_left hC hxPos hyl
        exact hp.trans (add_le_add le_rfl hdiv))
    rw [hCancel] at h
    exact h
  . have h := compare nicolasLogMertensOscillation (primeProfileMovingResidual alpha)
      2 ((2 * C) / x) x (by norm_num) (by positivity) (by
        intro y hyl _hyu
        have hp := (hX y (hxX.trans hyl)).2
        have hdiv := div_le_div_of_nonneg_left (show 0 <= 2 * C by positivity) hxPos hyl
        exact hp.trans (add_le_add le_rfl hdiv))
    rw [hCancelTwo] at h
    exact h

/-- For every fixed positive rank slope, RH is equivalent to a quarter-power
polylogarithmic bound for the positive area of the actual normalized residual. -/
theorem riemannHypothesis_iff_primeProfilePositiveArea_bound
    (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <->
      exists C B X : Real, 0 < C /\ forall x : Real, X <= x ->
        primeProfilePositiveArea alpha x <=
          ENNReal.ofReal (C * x ^ (1 / 4 : Real) * (Real.log x) ^ B) := by
  choose D hD hCompare using exists_eventually_primeProfilePositiveArea_compare alpha ha
  constructor
  . intro hRH
    have hZero := eventually_nicolasPositiveArea_eq_zero_of_RH hRH
    have hEv : Filter.Eventually (fun x : Real =>
        primeProfilePositiveArea alpha x <= ENNReal.ofReal ((D + 1) * x ^ (1 / 4 : Real)))
        atTop := by
      filter_upwards [hCompare, hZero, eventually_ge_atTop (1 : Real)] with x hc hz hx
      have hBound := hc.1
      rw [hz, mul_zero, zero_add] at hBound
      have hPower : 1 <= x ^ (1 / 4 : Real) := by
        simpa only [Real.rpow_zero] using
          Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (0 : Real) <= 1 / 4)
      apply hBound.trans
      apply ENNReal.ofReal_le_ofReal
      nlinarith only [hD, hPower]
    choose X hX using eventually_atTop.mp hEv
    refine Exists.intro (D + 1) (Exists.intro 0 (Exists.intro X
      (And.intro (by linarith) ?_)))
    intro x hx
    simpa only [Real.rpow_zero, mul_one] using hX x hx
  . intro hArea
    choose C B X hC hBound using hArea
    let B' : Real := max B 0
    let C' : Real := 2 * C + 2 * D
    have hC' : 0 < C' := by dsimp [C']; linarith
    have hEv : Filter.Eventually (fun x : Real =>
        nicolasPositiveArea x <= ENNReal.ofReal
          (C' * x ^ (1 / 4 : Real) * (Real.log x) ^ B')) atTop := by
      filter_upwards [hCompare, eventually_ge_atTop X,
        eventually_ge_atTop (3 : Real)] with x hc hxX hxThree
      have hxPos : 0 < x := by linarith
      have hxOne : 1 <= x := by linarith
      have hLog : 1 <= Real.log x :=
        ((Real.lt_log_iff_exp_lt hxPos).mpr (Real.exp_one_lt_three.trans_le hxThree)).le
      have hPower : 1 <= x ^ (1 / 4 : Real) := by
        simpa only [Real.rpow_zero] using
          Real.rpow_le_rpow_of_exponent_le hxOne (by norm_num : (0 : Real) <= 1 / 4)
      have hLogPower : (Real.log x) ^ B <= (Real.log x) ^ B' :=
        Real.rpow_le_rpow_of_exponent_le hLog (le_max_left B 0)
      have hLogOne : 1 <= (Real.log x) ^ B' := by
        simpa only [Real.rpow_zero] using
          Real.rpow_le_rpow_of_exponent_le hLog (le_max_right B 0)
      have hProductOne : 1 <= x ^ (1 / 4 : Real) * (Real.log x) ^ B' := by
        have h := mul_le_mul hPower hLogOne (by norm_num : (0 : Real) <= 1)
          (Real.rpow_nonneg hxPos.le _)
        simpa only [one_mul] using h
      have hProductCompare : x ^ (1 / 4 : Real) * (Real.log x) ^ B <=
          x ^ (1 / 4 : Real) * (Real.log x) ^ B' :=
        mul_le_mul_of_nonneg_left hLogPower (Real.rpow_nonneg hxPos.le _)
      have hPositive : 0 <= C * x ^ (1 / 4 : Real) * (Real.log x) ^ B := by positivity
      have hScalar :
          2 * (C * x ^ (1 / 4 : Real) * (Real.log x) ^ B) + 2 * D <=
          C' * x ^ (1 / 4 : Real) * (Real.log x) ^ B' := by
        have hMain := mul_le_mul_of_nonneg_left hProductCompare
          (show 0 <= 2 * C by positivity)
        have hReserve := mul_le_mul_of_nonneg_left hProductOne
          (show 0 <= 2 * D by positivity)
        dsimp [C']
        nlinarith only [hMain, hReserve]
      calc
        nicolasPositiveArea x <=
            ENNReal.ofReal (2 : Real) * primeProfilePositiveArea alpha x +
              ENNReal.ofReal (2 * D) := hc.2
        _ <= ENNReal.ofReal (2 : Real) *
            ENNReal.ofReal (C * x ^ (1 / 4 : Real) * (Real.log x) ^ B) +
              ENNReal.ofReal (2 * D) :=
          add_le_add (mul_le_mul_of_nonneg_left (hBound x hxX) (by positivity)) le_rfl
        _ = ENNReal.ofReal
            (2 * (C * x ^ (1 / 4 : Real) * (Real.log x) ^ B) + 2 * D) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
          simp only [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2)]
        _ <= _ := ENNReal.ofReal_le_ofReal hScalar
    choose Y hY using eventually_atTop.mp hEv
    exact riemannHypothesis_iff_nicolasPositiveArea_bound.mpr
      (Exists.intro C' (Exists.intro B' (Exists.intro Y (And.intro hC' hY))))

end PrimeFactorOscillations
