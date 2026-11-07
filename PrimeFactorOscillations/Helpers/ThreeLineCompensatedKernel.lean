/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.GCongr
import PrimeFactorOscillations.Helpers.CompensatedMomentRounding
import PrimeFactorOscillations.Helpers.ThreeLineMomentRatio

/-! # Full signed-kernel coercivity for compensated moment rounding -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def threeLineKernelXStep (x y z : Real) : Real :=
  threeLineWeight1 / (threeLineRadius1 * (threeLineRadius1 ^ 2 - x) *
    (threeLineRadius1 ^ 2 - y) * (threeLineRadius1 ^ 2 - z) ^ 2) +
  threeLineWeight2 / (threeLineRadius2 * (threeLineRadius2 ^ 2 - x) *
    (threeLineRadius2 ^ 2 - y) * (threeLineRadius2 ^ 2 - z) ^ 2) +
  threeLineWeight3 / (threeLineRadius3 * (threeLineRadius3 ^ 2 - x) *
    (threeLineRadius3 ^ 2 - y) * (threeLineRadius3 ^ 2 - z) ^ 2)

def threeLineKernelAnchorStep (z : Real) : Real :=
  threeLineHorizontalCubicDifference z z + threeLineHorizontalCubicDifference 0 z

theorem threeLineSignedOrdered_pos (u v w : Real)
    (hu : v <= u) (hv : 0 < v) (hw : 0 < w) :
    0 < threeLineWeight1 * u + threeLineWeight2 * v + threeLineWeight3 * w := by
  have hFirst : 0 <= threeLineWeight1 := by norm_num [threeLineWeight1]
  have hPair : 0 < threeLineWeight1 + threeLineWeight2 := by
    norm_num [threeLineWeight1, threeLineWeight2]
  have hThird : 0 < threeLineWeight3 := by norm_num [threeLineWeight3]
  have hPositive := mul_pos hPair hv
  have hDifference := mul_nonneg hFirst (sub_nonneg.mpr hu)
  have hLast := mul_pos hThird hw
  nlinarith only [hPositive, hDifference, hLast]

theorem threeLineSignedReciprocal_pos (d1 d2 d3 : Real)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) (hOrder : d1 <= d2) :
    0 < threeLineWeight1 / d1 + threeLineWeight2 / d2 + threeLineWeight3 / d3 := by
  have hIdentity : 1 / d1 - 1 / d2 = (d2 - d1) / (d1 * d2) := by
    field_simp [hd1.ne', hd2.ne']
  have hNonneg : 0 <= 1 / d1 - 1 / d2 := by
    rw [hIdentity]
    exact div_nonneg (sub_nonneg.mpr hOrder) (le_of_lt (mul_pos hd1 hd2))
  have h := threeLineSignedOrdered_pos (1 / d1) (1 / d2) (1 / d3)
    (by linarith) (div_pos (by norm_num) hd2) (div_pos (by norm_num) hd3)
  simpa only [div_eq_mul_inv, one_mul] using h

theorem threeLineKernel_one_xdifference (a x y z : Real) (ha : Not (a = 0))
    (hx : Not (a ^ 2 - x = 0)) (hy : Not (a ^ 2 - y = 0))
    (hz : Not (a ^ 2 - z = 0)) :
    1 / (a * (a ^ 2 - y) * (a ^ 2 - z) ^ 2) -
      1 / (a * (a ^ 2 - x) * (a ^ 2 - z) ^ 2) =
        (y - x) / (a * (a ^ 2 - x) * (a ^ 2 - y) * (a ^ 2 - z) ^ 2) := by
  field_simp [ha, hx, hy, hz]
  ring

theorem threeLineKernelXStep_pos (x y z : Real)
    (hx : x <= 1 / 4) (hy : y <= 1 / 4) (hz : z <= 1 / 4) :
    0 < threeLineKernelXStep x y z := by
  have hxd := threeLineMomentRatio_denominators_pos x hx
  have hyd := threeLineMomentRatio_denominators_pos y hy
  have hzd := threeLineMomentRatio_denominators_pos z hz
  have hx1 := hxd.1
  have hx2 := hxd.2.1
  have hy1 := hyd.1
  have hy2 := hyd.2.1
  have hz1 := hzd.1
  have hz2 := hzd.2.1
  let d1 := threeLineRadius1 * (threeLineRadius1 ^ 2 - x) *
    (threeLineRadius1 ^ 2 - y) * (threeLineRadius1 ^ 2 - z) ^ 2
  let d2 := threeLineRadius2 * (threeLineRadius2 ^ 2 - x) *
    (threeLineRadius2 ^ 2 - y) * (threeLineRadius2 ^ 2 - z) ^ 2
  let d3 := threeLineRadius3 * (threeLineRadius3 ^ 2 - x) *
    (threeLineRadius3 ^ 2 - y) * (threeLineRadius3 ^ 2 - z) ^ 2
  have hd1 : 0 < d1 := by
    dsimp [d1]
    exact mul_pos (mul_pos (mul_pos (by norm_num [threeLineRadius1]) hxd.1) hyd.1)
      (sq_pos_of_pos hzd.1)
  have hd2 : 0 < d2 := by
    dsimp [d2]
    exact mul_pos (mul_pos (mul_pos (by norm_num [threeLineRadius2]) hxd.2.1) hyd.2.1)
      (sq_pos_of_pos hzd.2.1)
  have hd3 : 0 < d3 := by
    dsimp [d3]
    exact mul_pos (mul_pos (mul_pos (by norm_num [threeLineRadius3]) hxd.2.2) hyd.2.2)
      (sq_pos_of_pos hzd.2.2)
  have hOrder : d1 <= d2 := by
    have hPositive : 0 <= threeLineRadius2 * (threeLineRadius2 ^ 2 - x) *
        (threeLineRadius2 ^ 2 - y) :=
      le_of_lt (mul_pos (mul_pos (by norm_num [threeLineRadius2]) hx2) hy2)
    norm_num [threeLineRadius2] at hPositive
    dsimp [d1, d2]
    gcongr <;> norm_num [threeLineRadius1, threeLineRadius2] <;> linarith
  exact threeLineSignedReciprocal_pos d1 d2 d3 hd1 hd2 hd3 hOrder

theorem threeLineSizeBiasedRemainder_xdifference (x y z : Real)
    (hx : x <= 1 / 4) (hy : y <= 1 / 4) (hz : z <= 1 / 4) :
    threeLineSizeBiasedRemainder y z - threeLineSizeBiasedRemainder x z =
      (y - x) * threeLineKernelXStep x y z := by
  have hxd := threeLineMomentRatio_denominators_pos x hx
  have hyd := threeLineMomentRatio_denominators_pos y hy
  have hzd := threeLineMomentRatio_denominators_pos z hz
  have ha1 : Not (threeLineRadius1 = 0) := by norm_num [threeLineRadius1]
  have ha2 : Not (threeLineRadius2 = 0) := by norm_num [threeLineRadius2]
  have ha3 : Not (threeLineRadius3 = 0) := by norm_num [threeLineRadius3]
  have h1 := congrArg (fun q : Real => threeLineWeight1 * q)
    (threeLineKernel_one_xdifference threeLineRadius1 x y z ha1 hxd.1.ne' hyd.1.ne' hzd.1.ne')
  have h2 := congrArg (fun q : Real => threeLineWeight2 * q)
    (threeLineKernel_one_xdifference threeLineRadius2 x y z ha2 hxd.2.1.ne' hyd.2.1.ne' hzd.2.1.ne')
  have h3 := congrArg (fun q : Real => threeLineWeight3 * q)
    (threeLineKernel_one_xdifference threeLineRadius3 x y z ha3 hxd.2.2.ne' hyd.2.2.ne' hzd.2.2.ne')
  unfold threeLineSizeBiasedRemainder threeLineKernelXStep
  simp only [div_eq_mul_inv] at h1 h2 h3
  simp only [div_eq_mul_inv]
  nlinarith only [h1, h2, h3]

theorem threeLineSizeBiasedRemainder_mono_x (x y z : Real)
    (hxy : x <= y) (hy : y <= 1 / 4) (hz : z <= 1 / 4) :
    threeLineSizeBiasedRemainder x z <= threeLineSizeBiasedRemainder y z := by
  have hx : x <= 1 / 4 := le_trans hxy hy
  have hIdentity := threeLineSizeBiasedRemainder_xdifference x y z hx hy hz
  have hProduct := mul_nonneg (sub_nonneg.mpr hxy)
    (le_of_lt (threeLineKernelXStep_pos x y z hx hy hz))
  linarith only [hIdentity, hProduct]

theorem threeLineSizeBiasedRemainder_origin :
    threeLineSizeBiasedRemainder 0 0 = threeLineParityCubicCoefficient := by
  norm_num [threeLineSizeBiasedRemainder, threeLineWeight1, threeLineWeight2,
    threeLineWeight3, threeLineRadius1, threeLineRadius2, threeLineRadius3,
    threeLineParityCubicCoefficient]

theorem threeLineKernel_one_anchor (a z : Real) (ha : Not (a = 0))
    (hz : Not (a ^ 2 - z = 0)) :
    1 / (a * (a ^ 2 - 0) * (a ^ 2 - z) ^ 2) -
      1 / (a * (a ^ 2 - 0) * (a ^ 2 - 0) ^ 2) =
        z * (1 / (a ^ 5 * (a ^ 2 - z) * (a ^ 2 - z)) +
          1 / (a ^ 5 * (a ^ 2 - 0) * (a ^ 2 - z))) := by
  field_simp [ha, hz]
  ring

theorem threeLineSizeBiasedRemainder_anchor_identity (z : Real) (hz : z <= 9 / 64) :
    threeLineSizeBiasedRemainder 0 z - threeLineParityCubicCoefficient =
      z * threeLineKernelAnchorStep z := by
  have hzd := threeLineMomentRatio_denominators_pos z (by linarith)
  have ha1 : Not (threeLineRadius1 = 0) := by norm_num [threeLineRadius1]
  have ha2 : Not (threeLineRadius2 = 0) := by norm_num [threeLineRadius2]
  have ha3 : Not (threeLineRadius3 = 0) := by norm_num [threeLineRadius3]
  have h1 := congrArg (fun q : Real => threeLineWeight1 * q)
    (threeLineKernel_one_anchor threeLineRadius1 z ha1 hzd.1.ne')
  have h2 := congrArg (fun q : Real => threeLineWeight2 * q)
    (threeLineKernel_one_anchor threeLineRadius2 z ha2 hzd.2.1.ne')
  have h3 := congrArg (fun q : Real => threeLineWeight3 * q)
    (threeLineKernel_one_anchor threeLineRadius3 z ha3 hzd.2.2.ne')
  rw [<- threeLineSizeBiasedRemainder_origin]
  unfold threeLineSizeBiasedRemainder threeLineKernelAnchorStep threeLineHorizontalCubicDifference
  simp only [div_eq_mul_inv] at h1 h2 h3
  simp only [div_eq_mul_inv]
  nlinarith only [h1, h2, h3]

theorem threeLineSizeBiasedRemainder_ge_tau (x z : Real)
    (hx : 0 <= x) (hxMax : x <= 1 / 4)
    (hz : 0 <= z) (hzMax : z <= 9 / 64) :
    threeLineParityCubicCoefficient <= threeLineSizeBiasedRemainder x z := by
  have hStep : 0 < threeLineKernelAnchorStep z :=
    add_pos (threeLineHorizontalCubicDifference_pos z z hzMax hzMax)
      (threeLineHorizontalCubicDifference_pos 0 z (by norm_num) hzMax)
  have hAnchor := threeLineSizeBiasedRemainder_anchor_identity z hzMax
  have hProduct := mul_nonneg hz (le_of_lt hStep)
  have hMon := threeLineSizeBiasedRemainder_mono_x 0 x z hx hxMax (by linarith)
  linarith only [hAnchor, hProduct, hMon]

theorem threeLineSizeBiasedRemainder_gt_tau (x z : Real)
    (hx : 0 <= x) (hxMax : x <= 1 / 4)
    (hz : 0 < z) (hzMax : z <= 9 / 64) :
    threeLineParityCubicCoefficient < threeLineSizeBiasedRemainder x z := by
  have hStep : 0 < threeLineKernelAnchorStep z :=
    add_pos (threeLineHorizontalCubicDifference_pos z z hzMax hzMax)
      (threeLineHorizontalCubicDifference_pos 0 z (by norm_num) hzMax)
  have hAnchor := threeLineSizeBiasedRemainder_anchor_identity z hzMax
  have hProduct := mul_pos hz hStep
  have hMon := threeLineSizeBiasedRemainder_mono_x 0 x z hx hxMax (by linarith)
  linarith only [hAnchor, hProduct, hMon]


def threeLineKernelLowC (y : Real) : Real := 2 - 2 * momentRoundThreshold - y
def threeLineKernelLowD (y : Real) : Real := 2 - y - momentRoundThreshold
def threeLineKernelLowL (t y : Real) : Real :=
  2 * t * momentRoundThreshold * threeLineKernelLowD y
def threeLineKernelLowNumerator (a t y : Real) : Real :=
  a ^ 2 * threeLineKernelLowC y - threeLineKernelLowL t y
def threeLineKernelLowDenominator (a t y : Real) : Real :=
  a * (a ^ 2 - t) ^ 2 * (a ^ 2 - t * y) * (a ^ 2 - t * momentRoundThreshold)
def threeLineKernelLowDifference (t y : Real) : Real :=
  threeLineWeight1 * (threeLineKernelLowNumerator threeLineRadius1 t y /
    threeLineKernelLowDenominator threeLineRadius1 t y) +
  threeLineWeight2 * (threeLineKernelLowNumerator threeLineRadius2 t y /
    threeLineKernelLowDenominator threeLineRadius2 t y) +
  threeLineWeight3 * (threeLineKernelLowNumerator threeLineRadius3 t y /
    threeLineKernelLowDenominator threeLineRadius3 t y)
def threeLineKernelParityCoefficient (t : Real) : Real :=
  momentRoundThreshold * threeLineSizeBiasedRemainder (t * momentRoundThreshold) t

theorem momentRoundThreshold_lt_three_tenths :
    momentRoundThreshold < 3 / 10 := by
  have hs := Real.sq_sqrt (show (0 : Real) <= 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : Real)
  dsimp [momentRoundThreshold]
  nlinarith

theorem threeLineKernelLow_geometry (y : Real) (_hy : 0 <= y)
    (hyMax : y <= momentRoundThreshold) :
    And (0 < threeLineKernelLowC y)
      (And (0 < threeLineKernelLowD y)
        (threeLineKernelLowD y <= (4 / 3) * threeLineKernelLowC y)) := by
  have hd := momentRoundThreshold_lt_three_tenths
  unfold threeLineKernelLowC threeLineKernelLowD
  constructor
  case left => linarith
  case right =>
    constructor <;> linarith

theorem threeLineKernelLow_L_bound (t y : Real)
    (ht : 0 <= t) (htMax : t <= 9 / 64)
    (hy : 0 <= y) (hyMax : y <= momentRoundThreshold) :
    And (0 <= threeLineKernelLowL t y)
      (threeLineKernelLowL t y <= (9 / 80) * threeLineKernelLowC y) := by
  have hG := threeLineKernelLow_geometry y hy hyMax
  have hd := momentRoundThreshold_bounds.1
  have hdMax := momentRoundThreshold_lt_three_tenths
  have hOne := _root_.mul_le_mul_of_nonneg_right htMax (le_of_lt hd)
  have hTwo := _root_.mul_le_mul_of_nonneg_left (le_of_lt hdMax)
    (show (0 : Real) <= 9 / 64 by norm_num)
  have hProduct : 2 * t * momentRoundThreshold <= 27 / 320 := by
    nlinarith only [hOne, hTwo]
  have hScale := _root_.mul_le_mul_of_nonneg_left hG.2.2
    (show 0 <= 2 * t * momentRoundThreshold by positivity)
  have hScale2 := _root_.mul_le_mul_of_nonneg_right hProduct (le_of_lt hG.1)
  unfold threeLineKernelLowL
  constructor
  case left =>
    exact mul_nonneg (show 0 <= 2 * t * momentRoundThreshold by positivity) (le_of_lt hG.2.1)
  case right => nlinarith only [hScale, hScale2]

theorem threeLineKernelLowNumerator_lower (a t y : Real)
    (ha : 1 / 2 <= a) (ht : 0 <= t) (htMax : t <= 9 / 64)
    (hy : 0 <= y) (hyMax : y <= momentRoundThreshold) :
    (a ^ 2 / 2) * threeLineKernelLowC y <= threeLineKernelLowNumerator a t y := by
  have hC := (threeLineKernelLow_geometry y hy hyMax).1
  have hL := (threeLineKernelLow_L_bound t y ht htMax hy hyMax).2
  have hA : 9 / 80 <= a ^ 2 / 2 := by nlinarith [sq_nonneg (a - 1 / 2)]
  have hScaled := _root_.mul_le_mul_of_nonneg_right hA (le_of_lt hC)
  unfold threeLineKernelLowNumerator
  nlinarith only [hL, hScaled]

theorem threeLineKernelLowNumerator_upper (a t y : Real)
    (ht : 0 <= t) (htMax : t <= 9 / 64)
    (hy : 0 <= y) (hyMax : y <= momentRoundThreshold) :
    threeLineKernelLowNumerator a t y <= a ^ 2 * threeLineKernelLowC y := by
  have hL := (threeLineKernelLow_L_bound t y ht htMax hy hyMax).1
  unfold threeLineKernelLowNumerator
  linarith

theorem threeLineKernelLowNumerator_pos (a t y : Real)
    (ha : 1 / 2 <= a) (ht : 0 <= t) (htMax : t <= 9 / 64)
    (hy : 0 <= y) (hyMax : y <= momentRoundThreshold) :
    0 < threeLineKernelLowNumerator a t y := by
  have hLower := threeLineKernelLowNumerator_lower a t y ha ht htMax hy hyMax
  have hC := (threeLineKernelLow_geometry y hy hyMax).1
  have haPos : 0 < a := by linarith
  have hProduct : 0 < (a ^ 2 / 2) * threeLineKernelLowC y := by positivity
  linarith only [hLower, hProduct]

theorem threeLineKernelLow_arguments (t y : Real)
    (ht : 0 <= t) (htMax : t <= 9 / 64)
    (_hy : 0 <= y) (hyMax : y <= momentRoundThreshold) :
    And (t <= 1 / 4)
      (And (t * y <= 1 / 4) (t * momentRoundThreshold <= 1 / 4)) := by
  have hd := momentRoundThreshold_bounds.2
  have hOne := _root_.mul_le_mul_of_nonneg_left (le_trans hyMax (le_of_lt hd)) ht
  have hTwo := _root_.mul_le_mul_of_nonneg_left (le_of_lt hd) ht
  constructor
  case left => linarith
  case right =>
    constructor <;> nlinarith only [hOne, hTwo, htMax]

theorem threeLineKernelLowDenominator_pos (a t y : Real) (ha : 0 < a)
    (ht : 0 < a ^ 2 - t) (hy : 0 < a ^ 2 - t * y)
    (hd : 0 < a ^ 2 - t * momentRoundThreshold) :
    0 < threeLineKernelLowDenominator a t y := by
  exact mul_pos (mul_pos (mul_pos ha (sq_pos_of_pos ht)) hy) hd

theorem threeLineKernelLowDenominator_order (t y : Real)
    (ht : 0 <= t) (htMax : t <= 9 / 64)
    (hy : 0 <= y) (hyMax : y <= momentRoundThreshold) :
    4 * threeLineKernelLowDenominator threeLineRadius1 t y <=
      threeLineKernelLowDenominator threeLineRadius2 t y := by
  have hArgs := threeLineKernelLow_arguments t y ht htMax hy hyMax
  have hT := threeLineMomentRatio_denominators_pos t hArgs.1
  have hY := threeLineMomentRatio_denominators_pos (t * y) hArgs.2.1
  have hD := threeLineMomentRatio_denominators_pos (t * momentRoundThreshold) hArgs.2.2
  have hD1 := threeLineKernelLowDenominator_pos threeLineRadius1 t y
    (by norm_num [threeLineRadius1]) hT.1 hY.1 hD.1
  have hPole (u : Real) (hu : 0 <= u) :
      (3 / 2) * (threeLineRadius1 ^ 2 - u) <= threeLineRadius2 ^ 2 - u := by
    norm_num [threeLineRadius1, threeLineRadius2]
    linarith
  have hPoleT := hPole t ht
  have hPoleY := hPole (t * y) (mul_nonneg ht hy)
  have hPoleD := hPole (t * momentRoundThreshold)
    (mul_nonneg ht (le_of_lt momentRoundThreshold_bounds.1))
  have hPrefix : 0 <= threeLineRadius2 * (threeLineRadius2 ^ 2 - t) ^ 2 *
      (threeLineRadius2 ^ 2 - t * y) :=
    le_of_lt (mul_pos (mul_pos (by norm_num [threeLineRadius2]) (sq_pos_of_pos hT.2.1)) hY.2.1)
  norm_num [threeLineRadius2] at hPrefix
  have hScaled : (81 / 16) * threeLineKernelLowDenominator threeLineRadius1 t y <=
      threeLineKernelLowDenominator threeLineRadius2 t y := by
    unfold threeLineKernelLowDenominator
    calc
      _ = threeLineRadius1 * ((3 / 2) * (threeLineRadius1 ^ 2 - t)) ^ 2 *
          ((3 / 2) * (threeLineRadius1 ^ 2 - t * y)) *
          ((3 / 2) * (threeLineRadius1 ^ 2 - t * momentRoundThreshold)) := by ring
      _ <= _ := by
        gcongr <;> norm_num [threeLineRadius1, threeLineRadius2] at * <;> nlinarith
  calc
    _ <= (81 / 16) * threeLineKernelLowDenominator threeLineRadius1 t y :=
      _root_.mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt hD1)
    _ <= _ := hScaled

theorem threeLineKernelLow_ratio_order (t y : Real)
    (ht : 0 <= t) (htMax : t <= 9 / 64)
    (hy : 0 <= y) (hyMax : y <= momentRoundThreshold) :
    threeLineKernelLowNumerator threeLineRadius2 t y /
        threeLineKernelLowDenominator threeLineRadius2 t y <=
      threeLineKernelLowNumerator threeLineRadius1 t y /
        threeLineKernelLowDenominator threeLineRadius1 t y := by
  have hArgs := threeLineKernelLow_arguments t y ht htMax hy hyMax
  have hT := threeLineMomentRatio_denominators_pos t hArgs.1
  have hY := threeLineMomentRatio_denominators_pos (t * y) hArgs.2.1
  have hD := threeLineMomentRatio_denominators_pos (t * momentRoundThreshold) hArgs.2.2
  have hd1 := threeLineKernelLowDenominator_pos threeLineRadius1 t y
    (by norm_num [threeLineRadius1]) hT.1 hY.1 hD.1
  have hd2 := threeLineKernelLowDenominator_pos threeLineRadius2 t y
    (by norm_num [threeLineRadius2]) hT.2.1 hY.2.1 hD.2.1
  have hC := (threeLineKernelLow_geometry y hy hyMax).1
  have hP1 := threeLineKernelLowNumerator_lower threeLineRadius1 t y
    (by norm_num [threeLineRadius1]) ht htMax hy hyMax
  have hP2 := threeLineKernelLowNumerator_upper threeLineRadius2 t y ht htMax hy hyMax
  have hDen := threeLineKernelLowDenominator_order t y ht htMax hy hyMax
  have hR : threeLineRadius2 ^ 2 <= 2 * threeLineRadius1 ^ 2 := by
    norm_num [threeLineRadius1, threeLineRadius2]
  have hCross :
      threeLineKernelLowNumerator threeLineRadius2 t y *
          threeLineKernelLowDenominator threeLineRadius1 t y <=
        threeLineKernelLowNumerator threeLineRadius1 t y *
          threeLineKernelLowDenominator threeLineRadius2 t y := by
    calc
      _ <= (threeLineRadius2 ^ 2 * threeLineKernelLowC y) *
          threeLineKernelLowDenominator threeLineRadius1 t y :=
        _root_.mul_le_mul_of_nonneg_right hP2 (le_of_lt hd1)
      _ = threeLineRadius2 ^ 2 *
          (threeLineKernelLowC y * threeLineKernelLowDenominator threeLineRadius1 t y) := by ring
      _ <= (2 * threeLineRadius1 ^ 2) *
          (threeLineKernelLowC y * threeLineKernelLowDenominator threeLineRadius1 t y) :=
        _root_.mul_le_mul_of_nonneg_right hR (le_of_lt (mul_pos hC hd1))
      _ = ((threeLineRadius1 ^ 2 / 2) * threeLineKernelLowC y) *
          (4 * threeLineKernelLowDenominator threeLineRadius1 t y) := by ring
      _ <= ((threeLineRadius1 ^ 2 / 2) * threeLineKernelLowC y) *
          threeLineKernelLowDenominator threeLineRadius2 t y :=
        _root_.mul_le_mul_of_nonneg_left hDen (by positivity)
      _ <= _ := _root_.mul_le_mul_of_nonneg_right hP1 (le_of_lt hd2)
  have hIdentity :
      threeLineKernelLowNumerator threeLineRadius1 t y /
          threeLineKernelLowDenominator threeLineRadius1 t y -
        threeLineKernelLowNumerator threeLineRadius2 t y /
          threeLineKernelLowDenominator threeLineRadius2 t y =
      (threeLineKernelLowNumerator threeLineRadius1 t y *
          threeLineKernelLowDenominator threeLineRadius2 t y -
        threeLineKernelLowNumerator threeLineRadius2 t y *
          threeLineKernelLowDenominator threeLineRadius1 t y) /
      (threeLineKernelLowDenominator threeLineRadius1 t y *
        threeLineKernelLowDenominator threeLineRadius2 t y) := by
    field_simp [hd1.ne', hd2.ne']
  have hNonneg : 0 <=
      threeLineKernelLowNumerator threeLineRadius1 t y /
          threeLineKernelLowDenominator threeLineRadius1 t y -
        threeLineKernelLowNumerator threeLineRadius2 t y /
          threeLineKernelLowDenominator threeLineRadius2 t y := by
    rw [hIdentity]
    exact div_nonneg (sub_nonneg.mpr hCross) (le_of_lt (mul_pos hd1 hd2))
  linarith only [hNonneg]

theorem threeLineKernelLowDifference_pos (t y : Real)
    (ht : 0 <= t) (htMax : t <= 9 / 64)
    (hy : 0 <= y) (hyMax : y <= momentRoundThreshold) :
    0 < threeLineKernelLowDifference t y := by
  have hArgs := threeLineKernelLow_arguments t y ht htMax hy hyMax
  have hT := threeLineMomentRatio_denominators_pos t hArgs.1
  have hY := threeLineMomentRatio_denominators_pos (t * y) hArgs.2.1
  have hD := threeLineMomentRatio_denominators_pos (t * momentRoundThreshold) hArgs.2.2
  have hd2 := threeLineKernelLowDenominator_pos threeLineRadius2 t y
    (by norm_num [threeLineRadius2]) hT.2.1 hY.2.1 hD.2.1
  have hd3 := threeLineKernelLowDenominator_pos threeLineRadius3 t y
    (by norm_num [threeLineRadius3]) hT.2.2 hY.2.2 hD.2.2
  exact threeLineSignedOrdered_pos _ _ _
    (threeLineKernelLow_ratio_order t y ht htMax hy hyMax)
    (div_pos (threeLineKernelLowNumerator_pos threeLineRadius2 t y
      (by norm_num [threeLineRadius2]) ht htMax hy hyMax) hd2)
    (div_pos (threeLineKernelLowNumerator_pos threeLineRadius3 t y
      (by norm_num [threeLineRadius3]) ht htMax hy hyMax) hd3)


theorem threeLineKernel_one_low_identity (a t y : Real) (ha : Not (a = 0))
    (ht : Not (a ^ 2 - t = 0)) (hy : Not (a ^ 2 - t * y = 0))
    (hd : Not (a ^ 2 - t * momentRoundThreshold = 0)) :
    (y - 1) ^ 2 / (a * (a ^ 2 - t * y) * (a ^ 2 - t) ^ 2) -
      momentRoundThreshold * (2 - y) /
        (a * (a ^ 2 - t * momentRoundThreshold) * (a ^ 2 - t) ^ 2) =
      (momentRoundThreshold - y) *
        (threeLineKernelLowNumerator a t y / threeLineKernelLowDenominator a t y) := by
  have hPolynomial :
      (y - 1) ^ 2 * (a ^ 2 - t * momentRoundThreshold) -
        momentRoundThreshold * (2 - y) * (a ^ 2 - t * y) =
      (momentRoundThreshold - y) *
        (a ^ 2 * (2 - 2 * momentRoundThreshold - y) -
          2 * t * momentRoundThreshold * (2 - y - momentRoundThreshold)) := by
    calc
      _ = (momentRoundThreshold - y) *
          (a ^ 2 * (2 - 2 * momentRoundThreshold - y) -
            2 * t * momentRoundThreshold * (2 - y - momentRoundThreshold)) +
          (a ^ 2 - t * momentRoundThreshold) *
            (2 * momentRoundThreshold ^ 2 - 4 * momentRoundThreshold + 1) := by ring
      _ = _ := by rw [momentRoundThreshold_equation]; ring
  unfold threeLineKernelLowNumerator threeLineKernelLowDenominator
    threeLineKernelLowC threeLineKernelLowL threeLineKernelLowD
  calc
    _ = ((y - 1) ^ 2 * (a ^ 2 - t * momentRoundThreshold) -
        momentRoundThreshold * (2 - y) * (a ^ 2 - t * y)) /
        (a * (a ^ 2 - t) ^ 2 * (a ^ 2 - t * y) *
          (a ^ 2 - t * momentRoundThreshold)) := by
      have hyComm : Not (a ^ 2 - y * t = 0) := by
        intro h
        apply hy
        nlinarith only [h]
      have hyNorm : Not (-(y * t) + a ^ 2 = 0) := by
        intro h
        apply hy
        nlinarith only [h]
      field_simp [ha, ht, hy, hd, hyComm, hyNorm] <;> ring
    _ = _ := by rw [hPolynomial]; ring

theorem threeLineKernel_low_identity (t y : Real)
    (ht : 0 <= t) (htMax : t <= 9 / 64)
    (hy : 0 <= y) (hyMax : y <= momentRoundThreshold) :
    (y - 1) ^ 2 * threeLineSizeBiasedRemainder (t * y) t -
      momentRoundThreshold * (2 - y) *
        threeLineSizeBiasedRemainder (t * momentRoundThreshold) t =
      (momentRoundThreshold - y) * threeLineKernelLowDifference t y := by
  have hArgs := threeLineKernelLow_arguments t y ht htMax hy hyMax
  have hT := threeLineMomentRatio_denominators_pos t hArgs.1
  have hY := threeLineMomentRatio_denominators_pos (t * y) hArgs.2.1
  have hD := threeLineMomentRatio_denominators_pos (t * momentRoundThreshold) hArgs.2.2
  have ha1 : Not (threeLineRadius1 = 0) := by norm_num [threeLineRadius1]
  have ha2 : Not (threeLineRadius2 = 0) := by norm_num [threeLineRadius2]
  have ha3 : Not (threeLineRadius3 = 0) := by norm_num [threeLineRadius3]
  have h1 := congrArg (fun q : Real => threeLineWeight1 * q)
    (threeLineKernel_one_low_identity threeLineRadius1 t y ha1 hT.1.ne' hY.1.ne' hD.1.ne')
  have h2 := congrArg (fun q : Real => threeLineWeight2 * q)
    (threeLineKernel_one_low_identity threeLineRadius2 t y ha2 hT.2.1.ne' hY.2.1.ne' hD.2.1.ne')
  have h3 := congrArg (fun q : Real => threeLineWeight3 * q)
    (threeLineKernel_one_low_identity threeLineRadius3 t y ha3 hT.2.2.ne' hY.2.2.ne' hD.2.2.ne')
  unfold threeLineSizeBiasedRemainder threeLineKernelLowDifference
  simp only [div_eq_mul_inv] at h1 h2 h3
  simp only [div_eq_mul_inv]
  nlinarith only [h1, h2, h3]

theorem threeLineKernelParityCoefficient_ge_tau (t : Real)
    (ht : 0 <= t) (htMax : t <= 9 / 64) :
    momentRoundThreshold * threeLineParityCubicCoefficient <= threeLineKernelParityCoefficient t := by
  have hd := momentRoundThreshold_bounds.1
  have hArgs := threeLineKernelLow_arguments t momentRoundThreshold ht htMax
    (le_of_lt hd) (le_refl _)
  have hFloor := threeLineSizeBiasedRemainder_ge_tau (t * momentRoundThreshold) t
    (mul_nonneg ht (le_of_lt hd)) hArgs.2.2 ht htMax
  exact _root_.mul_le_mul_of_nonneg_left hFloor (le_of_lt hd)

theorem threeLineKernelParityCoefficient_gt_tau (t : Real)
    (ht : 0 < t) (htMax : t <= 9 / 64) :
    momentRoundThreshold * threeLineParityCubicCoefficient < threeLineKernelParityCoefficient t := by
  have hd := momentRoundThreshold_bounds.1
  have hArgs := threeLineKernelLow_arguments t momentRoundThreshold (le_of_lt ht) htMax
    (le_of_lt hd) (le_refl _)
  have hFloor := threeLineSizeBiasedRemainder_gt_tau (t * momentRoundThreshold) t
    (mul_nonneg (le_of_lt ht) (le_of_lt hd)) hArgs.2.2 ht htMax
  exact _root_.mul_lt_mul_of_pos_left hFloor hd

theorem threeLineKernelParityCoefficient_pos (t : Real)
    (ht : 0 <= t) (htMax : t <= 9 / 64) :
    0 < threeLineKernelParityCoefficient t := by
  have hFloor := threeLineKernelParityCoefficient_ge_tau t ht htMax
  have hPositive := mul_pos momentRoundThreshold_bounds.1 threeLineParityCubicCoefficient_pos
  linarith only [hFloor, hPositive]

theorem threeLineKernelParityCoefficient_gt_delta (t : Real)
    (ht : 0 <= t) (htMax : t <= 9 / 64) :
    momentRoundThreshold < threeLineKernelParityCoefficient t := by
  have hFloor := threeLineKernelParityCoefficient_ge_tau t ht htMax
  have hTau : 1 < threeLineParityCubicCoefficient := by norm_num [threeLineParityCubicCoefficient]
  have hScaled := _root_.mul_lt_mul_of_pos_left hTau momentRoundThreshold_bounds.1
  nlinarith only [hFloor, hScaled]

theorem threeLineKernel_compensated_bounds (t y : Real)
    (ht : 0 < t) (htMax : t <= 9 / 64) (hy : 0 <= y) (hMax : t * y <= 1 / 4) :
    And (-y * (y - 1) ^ 2 * threeLineSizeBiasedRemainder (t * y) t <=
      threeLineKernelParityCoefficient t *
        (2 * y - y ^ 2 - momentRoundIndicator momentRoundThreshold y))
      (threeLineKernelParityCoefficient t *
        (2 * y - y ^ 2 - momentRoundIndicator momentRoundThreshold y) <=
          y * (y - 1) ^ 2 * threeLineSizeBiasedRemainder (t * y) t) := by
  classical
  have hCoeff := threeLineKernelParityCoefficient_pos t (le_of_lt ht) htMax
  have hYNonneg := mul_nonneg (le_of_lt ht) hy
  have hKernel : 0 < threeLineSizeBiasedRemainder (t * y) t :=
    lt_trans (by norm_num) (threeLineSizeBiasedRemainder_gt_one (t * y) t
      (And.intro hYNonneg hMax) (And.intro (le_of_lt ht) (by linarith)))
  have hEnergy := mul_nonneg (mul_nonneg hy (sq_nonneg (y - 1))) (le_of_lt hKernel)
  unfold momentRoundIndicator
  by_cases hCut : momentRoundThreshold <= y
  case pos =>
    rw [ite_eq_left hCut]
    have hXY := _root_.mul_le_mul_of_nonneg_left hCut (le_of_lt ht)
    have hMon := threeLineSizeBiasedRemainder_mono_x (t * momentRoundThreshold) (t * y) t
      hXY hMax (by linarith)
    have hArgs := threeLineKernelLow_arguments t momentRoundThreshold (le_of_lt ht) htMax
      (le_of_lt momentRoundThreshold_bounds.1) (le_refl _)
    have hAnchor : 0 <= threeLineSizeBiasedRemainder (t * momentRoundThreshold) t :=
      le_of_lt (lt_trans (by norm_num)
        (threeLineSizeBiasedRemainder_gt_one (t * momentRoundThreshold) t
          (And.intro (mul_nonneg (le_of_lt ht) (le_of_lt momentRoundThreshold_bounds.1)) hArgs.2.2)
          (And.intro (le_of_lt ht) hArgs.1)))
    have hComparison : threeLineKernelParityCoefficient t <=
        y * threeLineSizeBiasedRemainder (t * y) t :=
      mul_le_mul hCut hMon hAnchor hy
    have hProduct := mul_nonneg (sub_nonneg.mpr hComparison) (sq_nonneg (y - 1))
    have hOther := mul_nonneg (le_of_lt hCoeff) (sq_nonneg (y - 1))
    constructor <;> nlinarith only [hProduct, hOther, hEnergy]
  case neg =>
    rw [ite_eq_right hCut]
    have hSmall : y < momentRoundThreshold := lt_of_not_ge hCut
    have hLow := threeLineKernel_low_identity t y (le_of_lt ht) htMax hy (le_of_lt hSmall)
    have hPositive := threeLineKernelLowDifference_pos t y (le_of_lt ht) htMax hy (le_of_lt hSmall)
    have hLowEq : (y - 1) ^ 2 * threeLineSizeBiasedRemainder (t * y) t -
        (2 - y) * threeLineKernelParityCoefficient t =
        (momentRoundThreshold - y) * threeLineKernelLowDifference t y := by
      unfold threeLineKernelParityCoefficient
      nlinarith only [hLow]
    have hScaled := congrArg (fun q : Real => y * q) hLowEq
    have hProduct := mul_nonneg hy
      (mul_nonneg (sub_nonneg.mpr (le_of_lt hSmall)) (le_of_lt hPositive))
    have hMiddle := mul_nonneg (le_of_lt hCoeff)
      (mul_nonneg hy (show 0 <= 2 - y by
        have hThreshold := momentRoundThreshold_bounds.2
        linarith))
    constructor <;> nlinarith only [hScaled, hProduct, hMiddle, hEnergy]


theorem threeLineWeightedCompensatedKernel_deviation {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMax : forall i, Membership.mem S i -> t * y i <= 1 / 4)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i)) :
    threeLineKernelParityCoefficient t * abs (Finset.sum S (fun i => a i * y i) -
      Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) <=
        Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2 *
          threeLineSizeBiasedRemainder (t * y i) t) := by
  have hLedger := finiteWeightedCompensatedRound_ledger S a y momentRoundThreshold hMoment
  have hLower : -Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2 *
      threeLineSizeBiasedRemainder (t * y i) t) <=
      threeLineKernelParityCoefficient t * (Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) := by
    rw [<- hLedger, Finset.mul_sum, <- Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have h := _root_.mul_le_mul_of_nonneg_left
      (threeLineKernel_compensated_bounds t (y i) ht htMax (hy i hi) (hMax i hi)).1 (ha i hi)
    nlinarith only [h]
  have hUpper : threeLineKernelParityCoefficient t * (Finset.sum S (fun i => a i * y i) -
      Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) <=
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2 *
        threeLineSizeBiasedRemainder (t * y i) t) := by
    rw [<- hLedger, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := _root_.mul_le_mul_of_nonneg_left
      (threeLineKernel_compensated_bounds t (y i) ht htMax (hy i hi) (hMax i hi)).2 (ha i hi)
    nlinarith only [h]
  have hAbs := abs_le.mpr (And.intro hLower hUpper)
  simpa only [abs_mul,
    abs_of_nonneg (le_of_lt (threeLineKernelParityCoefficient_pos t (le_of_lt ht) htMax))] using hAbs

theorem threeLineWeightedCompensatedKernel_scaled {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i)) :
    threeLineKernelParityCoefficient t * t ^ 3 *
      abs (Finset.sum S (fun i => a i * x i) / t -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t))) <=
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2 * threeLineSizeBiasedRemainder (x i) t) := by
  have hNormalized : Finset.sum S (fun i => a i * (x i / t) ^ 2) =
      Finset.sum S (fun i => a i * (x i / t)) := by
    calc
      _ = Finset.sum S (fun i => a i * (x i) ^ 2) / t ^ 2 := by
        simp only [div_pow]
        exact finiteWeighted_div_sum S a (fun i => (x i) ^ 2) (t ^ 2)
      _ = Finset.sum S (fun i => a i * x i) / t := by
        rw [hMoment]
        field_simp [ht.ne']
      _ = _ := (finiteWeighted_div_sum S a x t).symm
  have hMax : forall i, Membership.mem S i -> t * (x i / t) <= 1 / 4 := by
    intro i hi
    have hTX : t * (x i / t) = x i := by field_simp [ht.ne']
    rw [hTX]
    exact (hx i hi).2
  have hRound := threeLineWeightedCompensatedKernel_deviation S a (fun i => x i / t) t ht htMax
    ha (fun i hi => div_nonneg (hx i hi).1 (le_of_lt ht)) hMax hNormalized
  rw [finiteWeighted_div_sum] at hRound
  have hScaled := _root_.mul_le_mul_of_nonneg_left hRound (pow_nonneg (le_of_lt ht) 3)
  have hEnergy : t ^ 3 * Finset.sum S (fun i => a i * (x i / t) * (x i / t - 1) ^ 2 *
      threeLineSizeBiasedRemainder (t * (x i / t)) t) =
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2 *
        threeLineSizeBiasedRemainder (x i) t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hTX : t * (x i / t) = x i := by field_simp [ht.ne']
    rw [hTX]
    have h := congrArg (fun q : Real => a i * q * threeLineSizeBiasedRemainder (x i) t)
      (finiteWeighted_rescale_energy (x i) t ht)
    nlinarith only [h]
  calc
    _ = t ^ 3 * (threeLineKernelParityCoefficient t *
        abs (Finset.sum S (fun i => a i * x i) / t -
          Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t)))) := by ring
    _ <= t ^ 3 * Finset.sum S (fun i => a i * (x i / t) * (x i / t - 1) ^ 2 *
        threeLineSizeBiasedRemainder (t * (x i / t)) t) := hScaled
    _ = _ := hEnergy

theorem threeLineWeightedKernel_ledger {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : t <= 1 / 4)
    (hx : forall i, Membership.mem S i -> x i <= 1 / 4)
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i)) :
    Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) =
      threeLineCharge * Finset.sum S a +
      threeLineSizeBiasedProfile t * Finset.sum S (fun i => a i * x i) +
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2 * threeLineSizeBiasedRemainder (x i) t) := by
  have hExpanded : Finset.sum S (fun i => a i * x i * threeLineSizeBiasedProfile (x i)) =
      threeLineSizeBiasedProfile t * Finset.sum S (fun i => a i * x i) +
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2 * threeLineSizeBiasedRemainder (x i) t) := by
    calc
      _ = Finset.sum S (fun i =>
          threeLineSizeBiasedProfile t * (a i * x i) +
          threeLineSizeBiasedSlope t * (a i * (x i) ^ 2) -
          (threeLineSizeBiasedSlope t * t) * (a i * x i) +
          a i * x i * (x i - t) ^ 2 * threeLineSizeBiasedRemainder (x i) t) := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := congrArg (fun q : Real => a i * x i * q)
          (threeLineSizeBiased_tangent_identity (x i) t (hx i hi) ht)
        nlinarith only [h]
      _ = threeLineSizeBiasedProfile t * Finset.sum S (fun i => a i * x i) +
          threeLineSizeBiasedSlope t * Finset.sum S (fun i => a i * (x i) ^ 2) -
          (threeLineSizeBiasedSlope t * t) * Finset.sum S (fun i => a i * x i) +
          Finset.sum S (fun i => a i * x i * (x i - t) ^ 2 * threeLineSizeBiasedRemainder (x i) t) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          <- Finset.mul_sum, <- Finset.mul_sum, <- Finset.mul_sum]
      _ = _ := by rw [hMoment]; ring
  rw [threeLineMomentRatio_phi_ledger S a x hx, hExpanded]
  ring

theorem threeLineWeightedCompensatedKernel_charge {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i)) :
    threeLineCharge * Finset.sum S a +
      threeLineSizeBiasedProfile t * Finset.sum S (fun i => a i * x i) +
      threeLineKernelParityCoefficient t * t ^ 3 *
        abs (Finset.sum S (fun i => a i * x i) / t -
          Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t))) <=
      Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) := by
  have hLedger := threeLineWeightedKernel_ledger S a x t (by linarith)
    (fun i hi => (hx i hi).2) hMoment
  have hLower := threeLineWeightedCompensatedKernel_scaled S a x t ht htMax ha hx hMoment
  nlinarith only [hLedger, hLower]

end PrimeFactorOscillations
