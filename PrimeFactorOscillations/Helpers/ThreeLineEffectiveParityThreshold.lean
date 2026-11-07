/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CompensatedMomentParityStability

/-! # An explicit range for the finite-height parity improvement -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def threeLineScaleNumerator (r d t : Real) : Real :=
  (d + 2) * r ^ 4 - (2 * d + 1) * r ^ 2 * t + d * t ^ 2

def threeLineScaleDenominator (r d t : Real) : Real :=
  r ^ 7 * (r ^ 2 - d * t) * (r ^ 2 - t) ^ 2

def threeLineScaleCoordinate (c r d t : Real) : Real :=
  c / (r * (r ^ 2 - d * t) * (r ^ 2 - t) ^ 2) - c / r ^ 7

theorem threeLineScale_arguments (r d t : Real) (hr : 1 / 2 <= r)
    (hd : And (0 <= d) (d <= 3 / 10)) (ht : And (0 <= t) (t <= 1 / 16)) :
    And (0 < r) (And (0 < r ^ 2 - d * t) (0 < r ^ 2 - t)) := by
  have hrSq : 1 / 4 <= r ^ 2 := by nlinarith
  have hdt : d * t <= 3 / 160 := by
    calc
      _ <= (3 / 10) * t := _root_.mul_le_mul_of_nonneg_right hd.2 ht.1
      _ <= (3 / 10) * (1 / 16) := _root_.mul_le_mul_of_nonneg_left ht.2 (by norm_num)
      _ = _ := by norm_num
  exact And.intro (by linarith) (And.intro (by linarith) (by linarith))

theorem threeLineScale_coordinate_identity (c r d t : Real)
    (hr : 0 < r) (hx : 0 < r ^ 2 - d * t) (hz : 0 < r ^ 2 - t) :
    threeLineScaleCoordinate c r d t * threeLineScaleDenominator r d t =
      t * c * threeLineScaleNumerator r d t := by
  have hxNorm : Not (-(d * t) + r ^ 2 = 0) := by intro h; linarith
  have hzNorm : Not (-t + r ^ 2 = 0) := by intro h; linarith
  unfold threeLineScaleCoordinate threeLineScaleDenominator threeLineScaleNumerator
  field_simp [hr.ne', hx.ne', hz.ne', hxNorm, hzNorm]
  ring

theorem threeLineScale_coordinate_upper (c r d t slope : Real) (ht : 0 <= t)
    (hr : 0 < r) (hx : 0 < r ^ 2 - d * t) (hz : 0 < r ^ 2 - t)
    (hSlope : c * threeLineScaleNumerator r d t <=
      slope * threeLineScaleDenominator r d t) :
    threeLineScaleCoordinate c r d t <= slope * t := by
  have hDen : 0 < threeLineScaleDenominator r d t := by
    unfold threeLineScaleDenominator
    exact mul_pos (mul_pos (pow_pos hr 7) hx) (sq_pos_of_pos hz)
  have hIdentity := threeLineScale_coordinate_identity c r d t hr hx hz
  have hScaled := _root_.mul_le_mul_of_nonneg_left hSlope ht
  by_contra hNot
  have hBad := lt_of_not_ge hNot
  have hProduct := _root_.mul_lt_mul_of_pos_right hBad hDen
  nlinarith only [hIdentity, hScaled, hProduct]

theorem threeLineScale_first_denominator (d t : Real)
    (hd : And (0 <= d) (d <= 3 / 10)) (ht : And (0 <= t) (t <= 1 / 16)) :
    1 / 16000 <= threeLineScaleDenominator threeLineRadius1 d t := by
  have hdt : d * t <= 3 / 160 := by
    calc
      _ <= (3 / 10) * t := _root_.mul_le_mul_of_nonneg_right hd.2 ht.1
      _ <= (3 / 10) * (1 / 16) := _root_.mul_le_mul_of_nonneg_left ht.2 (by norm_num)
      _ = _ := by norm_num
  have hr : (1 / 128 : Real) <= threeLineRadius1 ^ 7 := by norm_num [threeLineRadius1]
  have hx : 37 / 160 <= threeLineRadius1 ^ 2 - d * t := by
    norm_num [threeLineRadius1]
    linarith
  have hz : 3 / 16 <= threeLineRadius1 ^ 2 - t := by
    norm_num [threeLineRadius1]
    linarith
  have hPrefix : 0 <= threeLineRadius1 ^ 7 * (threeLineRadius1 ^ 2 - d * t) :=
    mul_nonneg (by linarith) (by linarith)
  calc
    _ <= (1 / 128 : Real) * (37 / 160) * (3 / 16) ^ 2 := by norm_num
    _ <= _ := by
      unfold threeLineScaleDenominator
      gcongr

theorem threeLineScale_first_numerator (d t : Real)
    (hd : And (0 <= d) (d <= 3 / 10)) (ht : And (0 <= t) (t <= 1 / 16)) :
    threeLineWeight1 * threeLineScaleNumerator threeLineRadius1 d t <= 3 / 16 := by

  have hd0 := hd.1
  have ht0 := ht.1
  have htSq : t ^ 2 <= 1 / 256 := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have hdtSq : d * t ^ 2 <= 3 / 2560 := by
    calc
      _ <= (3 / 10) * t ^ 2 := _root_.mul_le_mul_of_nonneg_right hd.2 (sq_nonneg t)
      _ <= (3 / 10) * (1 / 256) := _root_.mul_le_mul_of_nonneg_left htSq (by norm_num)
      _ = _ := by norm_num
  have hMiddle : 0 <= (2 * d + 1) * threeLineRadius1 ^ 2 * t := by positivity
  have hP : threeLineScaleNumerator threeLineRadius1 d t <= 3 / 20 := by
    norm_num [threeLineScaleNumerator, threeLineRadius1] at hMiddle
    norm_num [threeLineScaleNumerator, threeLineRadius1]
    nlinarith only [hMiddle, hdtSq, hd.2]
  calc
    _ <= threeLineWeight1 * (3 / 20) :=
      _root_.mul_le_mul_of_nonneg_left hP (by norm_num [threeLineWeight1])
    _ <= _ := by norm_num [threeLineWeight1]

theorem threeLineScale_first_increment (d t : Real)
    (hd : And (0 <= d) (d <= 3 / 10)) (ht : And (0 <= t) (t <= 1 / 16)) :
    threeLineScaleCoordinate threeLineWeight1 threeLineRadius1 d t <= 3000 * t := by
  have hArgs := threeLineScale_arguments threeLineRadius1 d t (by norm_num [threeLineRadius1]) hd ht
  have hDen := threeLineScale_first_denominator d t hd ht
  have hNum := threeLineScale_first_numerator d t hd ht
  exact threeLineScale_coordinate_upper _ _ _ _ 3000 ht.1 hArgs.1 hArgs.2.1 hArgs.2.2
    (by nlinarith only [hDen, hNum])

theorem threeLineScale_second_numerator_nonneg (d t : Real)
    (hd : And (0 <= d) (d <= 3 / 10)) (ht : And (0 <= t) (t <= 1 / 16)) :
    0 <= threeLineScaleNumerator threeLineRadius2 d t := by

  have hd0 := hd.1
  have ht0 := ht.1
  have hMiddle : (2 * d + 1) * threeLineRadius2 ^ 2 * t <=
      (8 / 5) * threeLineRadius2 ^ 2 * (1 / 16) := by
    gcongr <;> linarith [hd.1, hd.2, ht.1, ht.2]
  have hLast := mul_nonneg hd.1 (sq_nonneg t)
  norm_num [threeLineScaleNumerator, threeLineRadius2] at hMiddle
  norm_num [threeLineScaleNumerator, threeLineRadius2]
  nlinarith only [hMiddle, hLast, hd.1]

theorem threeLineScale_second_increment (d t : Real)
    (hd : And (0 <= d) (d <= 3 / 10)) (ht : And (0 <= t) (t <= 1 / 16)) :
    threeLineScaleCoordinate threeLineWeight2 threeLineRadius2 d t <= 0 := by
  have hArgs := threeLineScale_arguments threeLineRadius2 d t (by norm_num [threeLineRadius2]) hd ht
  have hNum := threeLineScale_second_numerator_nonneg d t hd ht
  have hSlope : threeLineWeight2 * threeLineScaleNumerator threeLineRadius2 d t <=
      0 * threeLineScaleDenominator threeLineRadius2 d t := by
    have h : threeLineWeight2 * threeLineScaleNumerator threeLineRadius2 d t <= 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by norm_num [threeLineWeight2]) hNum
    simpa only [zero_mul] using h
  simpa only [zero_mul] using
    threeLineScale_coordinate_upper _ _ _ _ 0 ht.1 hArgs.1 hArgs.2.1 hArgs.2.2 hSlope

theorem threeLineScale_third_denominator (d t : Real)
    (hd : And (0 <= d) (d <= 3 / 10)) (ht : And (0 <= t) (t <= 1 / 16)) :
    1 <= threeLineScaleDenominator threeLineRadius3 d t := by
  have hdt : d * t <= 3 / 160 := by
    calc
      _ <= (3 / 10) * t := _root_.mul_le_mul_of_nonneg_right hd.2 ht.1
      _ <= (3 / 10) * (1 / 16) := _root_.mul_le_mul_of_nonneg_left ht.2 (by norm_num)
      _ = _ := by norm_num
  have hr : (1 : Real) <= threeLineRadius3 ^ 7 := by norm_num [threeLineRadius3]
  have hx : 1 <= threeLineRadius3 ^ 2 - d * t := by norm_num [threeLineRadius3]; linarith
  have hz : 1 <= threeLineRadius3 ^ 2 - t := by norm_num [threeLineRadius3]; linarith
  have hPrefix : 0 <= threeLineRadius3 ^ 7 * (threeLineRadius3 ^ 2 - d * t) :=
    mul_nonneg (by linarith) (by linarith)
  calc
    _ = (1 : Real) * 1 * 1 ^ 2 := by norm_num
    _ <= _ := by
      unfold threeLineScaleDenominator
      gcongr

theorem threeLineScale_third_numerator (d t : Real)
    (hd : And (0 <= d) (d <= 3 / 10)) (ht : And (0 <= t) (t <= 1 / 16)) :
    threeLineWeight3 * threeLineScaleNumerator threeLineRadius3 d t <= 1 := by

  have hd0 := hd.1
  have ht0 := ht.1
  have htSq : t ^ 2 <= 1 / 256 := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have hdtSq : d * t ^ 2 <= 3 / 2560 := by
    calc
      _ <= (3 / 10) * t ^ 2 := _root_.mul_le_mul_of_nonneg_right hd.2 (sq_nonneg t)
      _ <= (3 / 10) * (1 / 256) := _root_.mul_le_mul_of_nonneg_left htSq (by norm_num)
      _ = _ := by norm_num
  have hMiddle : 0 <= (2 * d + 1) * threeLineRadius3 ^ 2 * t := by positivity
  have hP : threeLineScaleNumerator threeLineRadius3 d t <= 5 := by
    norm_num [threeLineScaleNumerator, threeLineRadius3] at hMiddle
    norm_num [threeLineScaleNumerator, threeLineRadius3]
    nlinarith only [hMiddle, hdtSq, hd.2]
  calc
    _ <= threeLineWeight3 * 5 := _root_.mul_le_mul_of_nonneg_left hP (by norm_num [threeLineWeight3])
    _ <= _ := by norm_num [threeLineWeight3]

theorem threeLineScale_third_increment (d t : Real)
    (hd : And (0 <= d) (d <= 3 / 10)) (ht : And (0 <= t) (t <= 1 / 16)) :
    threeLineScaleCoordinate threeLineWeight3 threeLineRadius3 d t <= t := by
  have hArgs := threeLineScale_arguments threeLineRadius3 d t (by norm_num [threeLineRadius3]) hd ht
  have hDen := threeLineScale_third_denominator d t hd ht
  have hNum := threeLineScale_third_numerator d t hd ht
  have h := threeLineScale_coordinate_upper _ _ _ _ 1 ht.1 hArgs.1 hArgs.2.1 hArgs.2.2
    (show threeLineWeight3 * threeLineScaleNumerator threeLineRadius3 d t <=
      1 * threeLineScaleDenominator threeLineRadius3 d t by nlinarith only [hDen, hNum])
  simpa only [one_mul] using h

theorem threeLineKernelParityCoefficient_increment (t : Real) :
    threeLineKernelParityCoefficient t -
      momentRoundThreshold * threeLineParityCubicCoefficient =
    momentRoundThreshold *
      (threeLineScaleCoordinate threeLineWeight1 threeLineRadius1 momentRoundThreshold t +
        threeLineScaleCoordinate threeLineWeight2 threeLineRadius2 momentRoundThreshold t +
        threeLineScaleCoordinate threeLineWeight3 threeLineRadius3 momentRoundThreshold t) := by
  have hOrigin : threeLineWeight1 / threeLineRadius1 ^ 7 +
      threeLineWeight2 / threeLineRadius2 ^ 7 +
      threeLineWeight3 / threeLineRadius3 ^ 7 = threeLineParityCubicCoefficient := by
    norm_num [threeLineWeight1, threeLineWeight2, threeLineWeight3,
      threeLineRadius1, threeLineRadius2, threeLineRadius3, threeLineParityCubicCoefficient]
  rw [<- hOrigin]
  unfold threeLineKernelParityCoefficient threeLineSizeBiasedRemainder threeLineScaleCoordinate
  ring

theorem threeLineKernelParityCoefficient_explicit_increment (t : Real)
    (ht : And (0 <= t) (t <= 1 / 16)) :
    threeLineKernelParityCoefficient t -
      momentRoundThreshold * threeLineParityCubicCoefficient <= 1024 * t := by
  have hd : And (0 <= momentRoundThreshold) (momentRoundThreshold <= 3 / 10) :=
    And.intro (le_of_lt momentRoundThreshold_bounds.1)
      (le_of_lt momentRoundThreshold_lt_three_tenths)
  have h1 := threeLineScale_first_increment momentRoundThreshold t hd ht
  have h2 := threeLineScale_second_increment momentRoundThreshold t hd ht
  have h3 := threeLineScale_third_increment momentRoundThreshold t hd ht
  have hSum :
      threeLineScaleCoordinate threeLineWeight1 threeLineRadius1 momentRoundThreshold t +
        threeLineScaleCoordinate threeLineWeight2 threeLineRadius2 momentRoundThreshold t +
        threeLineScaleCoordinate threeLineWeight3 threeLineRadius3 momentRoundThreshold t <=
      3001 * t := by linarith
  have ht0 := ht.1
  have hFirst := _root_.mul_le_mul_of_nonneg_left hSum hd.1
  have hSecond := _root_.mul_le_mul_of_nonneg_right hd.2 (show 0 <= 3001 * t by positivity)
  rw [threeLineKernelParityCoefficient_increment]
  nlinarith only [hFirst, hSecond, ht.1]

theorem momentRoundThreshold_gt_nine_thirtyseconds :
    9 / 32 < momentRoundThreshold := by
  have hLower := momentRoundThreshold_gt_quarter
  have hSquare := sq_nonneg (momentRoundThreshold - 1 / 4)
  nlinarith only [hLower, hSquare, momentRoundThreshold_equation]

theorem threeLineParityStability_margin_gt_four :
    4 < threeLineParityCubicCoefficient * (momentRoundThreshold - 1 / 4) := by
  have hTau : 128 < threeLineParityCubicCoefficient := by norm_num [threeLineParityCubicCoefficient]
  have hGamma : 1 / 32 < momentRoundThreshold - 1 / 4 := by
    linarith [momentRoundThreshold_gt_nine_thirtyseconds]
  have hGammaPos : 0 < momentRoundThreshold - 1 / 4 := by linarith
  have hFirst := _root_.mul_lt_mul_of_pos_left hGamma (show (0 : Real) < 128 by norm_num)
  have hSecond := _root_.mul_lt_mul_of_pos_right hTau hGammaPos
  nlinarith only [hFirst, hSecond]

theorem threeLineParityStability_explicit_margin (budget t : Real) (hBudget : 0 < budget)
    (ht : And (0 <= t) (t <= 1 / 16)) (hCutoff : 1024 * budget * t <= 1) :
    threeLineKernelParityCoefficient t + 3 / budget <
      threeLineParityCubicCoefficient *
        (momentRoundThreshold + (momentRoundThreshold - 1 / 4) / budget) := by
  have hIncrement := threeLineKernelParityCoefficient_explicit_increment t ht
  have hMargin := threeLineParityStability_margin_gt_four
  have hScaled := _root_.mul_le_mul_of_nonneg_right hIncrement (le_of_lt hBudget)
  have hCancel : ((momentRoundThreshold - 1 / 4) / budget) * budget =
      momentRoundThreshold - 1 / 4 := by field_simp [hBudget.ne']
  have hTauCancel := congrArg (fun v : Real => threeLineParityCubicCoefficient * v) hCancel
  have hThree : (3 / budget) * budget = 3 := by field_simp [hBudget.ne']
  by_contra hNot
  have hBad := le_of_not_gt hNot
  have hBadScaled := _root_.mul_le_mul_of_nonneg_right hBad (le_of_lt hBudget)
  nlinarith only [hScaled, hMargin, hCutoff, hTauCancel, hThree, hBadScaled]

end PrimeFactorOscillations
