/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FunProp
import PrimeFactorOscillations.Helpers.ThreeLineParityGeometry

/-! # The sharp cubic scale of the fixed three-line parity defect

The negative second-pole term remains in the exact rational tail and its
divided difference. Its sign is controlled jointly with the first pole.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def threeLineParityCubicCoefficient : Real :=
  37413639865876325411850661752657392635 / 263902928706162612461624933697712128

def threeLineHorizontalCubicTail (x : Real) : Real :=
  threeLineWeight1 / (threeLineRadius1 ^ 5 * (threeLineRadius1 ^ 2 - x)) +
    threeLineWeight2 / (threeLineRadius2 ^ 5 * (threeLineRadius2 ^ 2 - x)) +
    threeLineWeight3 / (threeLineRadius3 ^ 5 * (threeLineRadius3 ^ 2 - x))

def threeLineHorizontalCubicDifference (x y : Real) : Real :=
  threeLineWeight1 / (threeLineRadius1 ^ 5 * (threeLineRadius1 ^ 2 - x) *
    (threeLineRadius1 ^ 2 - y)) +
  threeLineWeight2 / (threeLineRadius2 ^ 5 * (threeLineRadius2 ^ 2 - x) *
    (threeLineRadius2 ^ 2 - y)) +
  threeLineWeight3 / (threeLineRadius3 ^ 5 * (threeLineRadius3 ^ 2 - x) *
    (threeLineRadius3 ^ 2 - y))

def threeLineParityCubicScale (N : Real) : Real := (2 * N - 1) / (N ^ 2 * (N - 1) ^ 2)

def threeLineParityNormalizedCost (N M : Real) : Real :=
  (N ^ 2 * threeLineHorizontalCubicTail (M / (N - 1)) -
    (N - 1) ^ 2 * threeLineHorizontalCubicTail (M / N)) / (2 * N - 1)

theorem threeLineParityCubicCoefficient_pos : 0 < threeLineParityCubicCoefficient := by
  norm_num [threeLineParityCubicCoefficient]

theorem threeLineHorizontalCubicTail_zero :
    threeLineHorizontalCubicTail 0 = threeLineParityCubicCoefficient := by
  norm_num [threeLineHorizontalCubicTail, threeLineParityCubicCoefficient,
    threeLineWeight1, threeLineWeight2, threeLineWeight3,
    threeLineRadius1, threeLineRadius2, threeLineRadius3]

theorem threeLineHorizontal_one_cubic (a x : Real) (ha : Not (a = 0))
    (hx : Not (a ^ 2 - x = 0)) :
    a / (a ^ 2 - x) = 1 / a + x / a ^ 3 + x ^ 2 / a ^ 5 +
      x ^ 3 / (a ^ 5 * (a ^ 2 - x)) := by
  field_simp [ha, hx]
  ring

theorem threeLineHorizontal_one_cubic_difference (a x y : Real) (ha : Not (a = 0))
    (hx : Not (a ^ 2 - x = 0)) (hy : Not (a ^ 2 - y = 0)) :
    1 / (a ^ 5 * (a ^ 2 - y)) - 1 / (a ^ 5 * (a ^ 2 - x)) =
      (y - x) / (a ^ 5 * (a ^ 2 - x) * (a ^ 2 - y)) := by
  field_simp [ha, hx, hy]
  ring

theorem threeLineHorizontal_cubic_identity (x : Real) (hx : x <= 9 / 64) :
    threeLineHorizontalProfile x = threeLineCharge + threeLineHorizontalSlope 0 * x +
      threeLineHorizontalVarianceCoefficient * x ^ 2 + x ^ 3 * threeLineHorizontalCubicTail x := by
  have hd := threeLineHorizontal_denominators_pos x hx
  have ha1 : Not (threeLineRadius1 = 0) := by norm_num [threeLineRadius1]
  have ha2 : Not (threeLineRadius2 = 0) := by norm_num [threeLineRadius2]
  have ha3 : Not (threeLineRadius3 = 0) := by norm_num [threeLineRadius3]
  have h1 := congrArg (fun q : Real => threeLineWeight1 * q)
    (threeLineHorizontal_one_cubic threeLineRadius1 x ha1 hd.1.ne')
  have h2 := congrArg (fun q : Real => threeLineWeight2 * q)
    (threeLineHorizontal_one_cubic threeLineRadius2 x ha2 hd.2.1.ne')
  have h3 := congrArg (fun q : Real => threeLineWeight3 * q)
    (threeLineHorizontal_one_cubic threeLineRadius3 x ha3 hd.2.2.ne')
  have hG : threeLineCharge = threeLineWeight1 / threeLineRadius1 +
      threeLineWeight2 / threeLineRadius2 + threeLineWeight3 / threeLineRadius3 := by
    norm_num [threeLineCharge, threeLineWeight1, threeLineWeight2, threeLineWeight3,
      threeLineRadius1, threeLineRadius2, threeLineRadius3]
  have hL : threeLineHorizontalSlope 0 = threeLineWeight1 / threeLineRadius1 ^ 3 +
      threeLineWeight2 / threeLineRadius2 ^ 3 + threeLineWeight3 / threeLineRadius3 ^ 3 := by
    norm_num [threeLineHorizontalSlope, threeLineWeight1, threeLineWeight2, threeLineWeight3,
      threeLineRadius1, threeLineRadius2, threeLineRadius3]
  have hS : threeLineHorizontalVarianceCoefficient = threeLineWeight1 / threeLineRadius1 ^ 5 +
      threeLineWeight2 / threeLineRadius2 ^ 5 + threeLineWeight3 / threeLineRadius3 ^ 5 := by
    norm_num [threeLineHorizontalVarianceCoefficient, threeLineWeight1, threeLineWeight2, threeLineWeight3,
      threeLineRadius1, threeLineRadius2, threeLineRadius3]
  rw [hG, hL, hS]
  unfold threeLineHorizontalProfile threeLineHorizontalCubicTail
  simp only [div_eq_mul_inv] at h1 h2 h3
  simp only [div_eq_mul_inv]
  nlinarith only [h1, h2, h3]

theorem threeLineHorizontalResidual_cubic_identity (x : Real) (hx : x <= 9 / 64) :
    threeLineHorizontalResidualProfile x =
      threeLineCharge + threeLineHorizontalSlope 0 * x + x ^ 3 * threeLineHorizontalCubicTail x := by
  unfold threeLineHorizontalResidualProfile
  rw [threeLineHorizontal_cubic_identity x hx]
  ring

theorem threeLineHorizontalCubicTail_difference (x y : Real)
    (hx : x <= 9 / 64) (hy : y <= 9 / 64) :
    threeLineHorizontalCubicTail y - threeLineHorizontalCubicTail x =
      (y - x) * threeLineHorizontalCubicDifference x y := by
  have hd := threeLineHorizontal_denominators_pos x hx
  have he := threeLineHorizontal_denominators_pos y hy
  have ha1 : Not (threeLineRadius1 = 0) := by norm_num [threeLineRadius1]
  have ha2 : Not (threeLineRadius2 = 0) := by norm_num [threeLineRadius2]
  have ha3 : Not (threeLineRadius3 = 0) := by norm_num [threeLineRadius3]
  have h1 := congrArg (fun q : Real => threeLineWeight1 * q)
    (threeLineHorizontal_one_cubic_difference threeLineRadius1 x y ha1 hd.1.ne' he.1.ne')
  have h2 := congrArg (fun q : Real => threeLineWeight2 * q)
    (threeLineHorizontal_one_cubic_difference threeLineRadius2 x y ha2 hd.2.1.ne' he.2.1.ne')
  have h3 := congrArg (fun q : Real => threeLineWeight3 * q)
    (threeLineHorizontal_one_cubic_difference threeLineRadius3 x y ha3 hd.2.2.ne' he.2.2.ne')
  unfold threeLineHorizontalCubicTail threeLineHorizontalCubicDifference
  simp only [div_eq_mul_inv] at h1 h2 h3
  simp only [div_eq_mul_inv]
  nlinarith only [h1, h2, h3]

theorem threeLineHorizontalCubicDifference_pos (x y : Real)
    (hx : x <= 9 / 64) (hy : y <= 9 / 64) :
    0 < threeLineHorizontalCubicDifference x y := by
  have hxd := threeLineHorizontal_denominators_pos x hx
  have hyd := threeLineHorizontal_denominators_pos y hy
  have h1x := hxd.1
  have h2x := hxd.2.1
  have h3x := hxd.2.2
  have h1y := hyd.1
  have h2y := hyd.2.1
  have h3y := hyd.2.2
  let d1 := threeLineRadius1 ^ 5 * (threeLineRadius1 ^ 2 - x) * (threeLineRadius1 ^ 2 - y)
  let d2 := threeLineRadius2 ^ 5 * (threeLineRadius2 ^ 2 - x) * (threeLineRadius2 ^ 2 - y)
  let d3 := threeLineRadius3 ^ 5 * (threeLineRadius3 ^ 2 - x) * (threeLineRadius3 ^ 2 - y)
  have hp1 : 0 < threeLineRadius1 ^ 5 := by norm_num [threeLineRadius1]
  have hp2 : 0 < threeLineRadius2 ^ 5 := by norm_num [threeLineRadius2]
  have hp3 : 0 < threeLineRadius3 ^ 5 := by norm_num [threeLineRadius3]
  have hd1 : 0 < d1 := mul_pos (mul_pos hp1 h1x) h1y
  have hd2 : 0 < d2 := mul_pos (mul_pos hp2 h2x) h2y
  have hd3 : 0 < d3 := mul_pos (mul_pos hp3 h3x) h3y
  have hp12 : threeLineRadius1 ^ 5 <= threeLineRadius2 ^ 5 := by
    norm_num [threeLineRadius1, threeLineRadius2]
  have hx12 : threeLineRadius1 ^ 2 - x <= threeLineRadius2 ^ 2 - x := by
    norm_num [threeLineRadius1, threeLineRadius2]
  have hy12 : threeLineRadius1 ^ 2 - y <= threeLineRadius2 ^ 2 - y := by
    norm_num [threeLineRadius1, threeLineRadius2]
  have hd12 : d1 <= d2 :=
    mul_le_mul (mul_le_mul hp12 hx12 (le_of_lt h1x) (le_of_lt hp2)) hy12
      (le_of_lt h1y) (le_of_lt (mul_pos hp2 h2x))
  have hc1 : 0 < threeLineWeight1 := by norm_num [threeLineWeight1]
  have hc3 : 0 < threeLineWeight3 := by norm_num [threeLineWeight3]
  have hc12 : 0 < threeLineWeight1 + threeLineWeight2 := by
    norm_num [threeLineWeight1, threeLineWeight2]
  have hNum : 0 < threeLineWeight1 * d2 + threeLineWeight2 * d1 := by
    have hPos := mul_pos hc12 hd1
    have hDelta := mul_nonneg (le_of_lt hc1) (sub_nonneg.mpr hd12)
    nlinarith
  have hEq : (threeLineWeight1 / d1 + threeLineWeight2 / d2) * (d1 * d2) =
      threeLineWeight1 * d2 + threeLineWeight2 * d1 := by
    field_simp [hd1.ne', hd2.ne']
  have hPair : 0 < threeLineWeight1 / d1 + threeLineWeight2 / d2 := by
    by_contra h
    have hNonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h)
      (le_of_lt (mul_pos hd1 hd2))
    rw [hEq] at hNonpos
    linarith
  change 0 < threeLineWeight1 / d1 + threeLineWeight2 / d2 + threeLineWeight3 / d3
  linarith [div_pos hc3 hd3]

theorem threeLineHorizontalCubicTail_mono (x y : Real) (hxy : x <= y)
    (hx : x <= 9 / 64) (hy : y <= 9 / 64) :
    threeLineHorizontalCubicTail x <= threeLineHorizontalCubicTail y := by
  have h := threeLineHorizontalCubicTail_difference x y hx hy
  have hp := mul_nonneg (sub_nonneg.mpr hxy)
    (le_of_lt (threeLineHorizontalCubicDifference_pos x y hx hy))
  linarith

theorem threeLineHorizontalCubicTail_strict (x y : Real) (hxy : x < y)
    (hx : x <= 9 / 64) (hy : y <= 9 / 64) :
    threeLineHorizontalCubicTail x < threeLineHorizontalCubicTail y := by
  have h := threeLineHorizontalCubicTail_difference x y hx hy
  have hp := mul_pos (sub_pos.mpr hxy) (threeLineHorizontalCubicDifference_pos x y hx hy)
  linarith

theorem threeLineParityCubicScale_pos (N : Real) (hN : 1 < N) :
    0 < threeLineParityCubicScale N := by
  have hNp : 0 < N := by linarith
  have hQp : 0 < N - 1 := by linarith
  unfold threeLineParityCubicScale
  exact div_pos (by linarith) (mul_pos (pow_pos hNp 2) (pow_pos hQp 2))

theorem threeLineParityNormalizedCost_identity (N M : Real) (hN : 1 < N) :
    threeLineParityNormalizedCost N M = threeLineHorizontalCubicTail (M / N) +
      (N ^ 2 / (2 * N - 1)) *
        (threeLineHorizontalCubicTail (M / (N - 1)) - threeLineHorizontalCubicTail (M / N)) := by
  have hd : Not (2 * N - 1 = 0) := by linarith
  unfold threeLineParityNormalizedCost
  generalize threeLineHorizontalCubicTail (M / N) = A
  generalize threeLineHorizontalCubicTail (M / (N - 1)) = B
  generalize hDen : 2 * N - 1 = D at *
  field_simp [hd]
  subst D
  ring

theorem threeLineParityNormalizedCost_zero (N : Real) (hN : 1 < N) :
    threeLineParityNormalizedCost N 0 = threeLineParityCubicCoefficient := by
  rw [threeLineParityNormalizedCost_identity N 0 hN]
  simp [threeLineHorizontalCubicTail_zero]

theorem threeLineParityNormalizedCost_continuousAt_zero (N : Real) :
    ContinuousAt (fun M : Real => threeLineParityNormalizedCost N M) 0 := by
  unfold threeLineParityNormalizedCost threeLineHorizontalCubicTail
  fun_prop (disch := norm_num [threeLineRadius1, threeLineRadius2, threeLineRadius3])

theorem threeLineParityNormalizedCost_origin_limit (N : Real) (hN : 1 < N) :
    Filter.Tendsto (fun M : Real => threeLineParityNormalizedCost N M)
      (nhds 0) (nhds threeLineParityCubicCoefficient) := by
  have h := (threeLineParityNormalizedCost_continuousAt_zero N).tendsto
  rw [threeLineParityNormalizedCost_zero N hN] at h
  exact h

theorem threeLineParityCost_cubic_factorization (N M : Real) (hN : 1 < N) (hM : 0 <= M)
    (hMax : M <= (9 / 64 : Real) * (N - 1)) :
    threeLineParityCost N M = threeLineParityCubicScale N * M ^ 3 *
      threeLineParityNormalizedCost N M := by
  have hMeans := threeLineParityCost_means N M hN hM hMax
  have hNp : Not (N = 0) := by linarith
  have hQp : Not (N - 1 = 0) := by linarith
  have hDp : Not (2 * N - 1 = 0) := by linarith
  unfold threeLineParityCost
  rw [threeLineHorizontalResidual_cubic_identity _ hMeans.2.1.2,
    threeLineHorizontalResidual_cubic_identity _ hMeans.1.2]
  unfold threeLineParityCubicScale threeLineParityNormalizedCost
  generalize threeLineHorizontalCubicTail (M / N) = A
  generalize threeLineHorizontalCubicTail (M / (N - 1)) = B
  generalize hDen : 2 * N - 1 = D at *
  field_simp [hNp, hQp, hDp]
  subst D
  ring

theorem threeLineParityNormalizedCost_ge (N M : Real) (hN : 1 < N) (hM : 0 <= M)
    (hMax : M <= (9 / 64 : Real) * (N - 1)) :
    threeLineParityCubicCoefficient <= threeLineParityNormalizedCost N M := by
  have hMeans := threeLineParityCost_means N M hN hM hMax
  have hQp : 0 < N - 1 := by linarith
  have hDp : 0 < 2 * N - 1 := by linarith
  have hOrder : M / N <= M / (N - 1) := by
    apply (_root_.mul_le_mul_iff_of_pos_left hQp).mp
    rw [hMeans.2.2]
    nlinarith [hMeans.1.1]
  have hMono := threeLineHorizontalCubicTail_mono (M / N) (M / (N - 1)) hOrder
    hMeans.1.2 hMeans.2.1.2
  have hLower := threeLineHorizontalCubicTail_mono 0 (M / N) hMeans.1.1
    (by norm_num) hMeans.1.2
  rw [threeLineHorizontalCubicTail_zero] at hLower
  have hExtra := mul_nonneg (div_nonneg (sq_nonneg N) (le_of_lt hDp))
    (sub_nonneg.mpr hMono)
  rw [threeLineParityNormalizedCost_identity N M hN]
  linarith

theorem threeLineParityNormalizedCost_gt (N M : Real) (hN : 1 < N) (hM : 0 < M)
    (hMax : M <= (9 / 64 : Real) * (N - 1)) :
    threeLineParityCubicCoefficient < threeLineParityNormalizedCost N M := by
  have hMeans := threeLineParityCost_means N M hN (le_of_lt hM) hMax
  have hQp : 0 < N - 1 := by linarith
  have hDp : 0 < 2 * N - 1 := by linarith
  have hOrder : M / N <= M / (N - 1) := by
    apply (_root_.mul_le_mul_iff_of_pos_left hQp).mp
    rw [hMeans.2.2]
    nlinarith [hMeans.1.1]
  have hMono := threeLineHorizontalCubicTail_mono (M / N) (M / (N - 1)) hOrder
    hMeans.1.2 hMeans.2.1.2
  have hLower := threeLineHorizontalCubicTail_strict 0 (M / N) (div_pos hM (by linarith))
    (by norm_num) hMeans.1.2
  rw [threeLineHorizontalCubicTail_zero] at hLower
  have hExtra := mul_nonneg (div_nonneg (sq_nonneg N) (le_of_lt hDp))
    (sub_nonneg.mpr hMono)
  rw [threeLineParityNormalizedCost_identity N M hN]
  linarith

theorem threeLineParityCost_cubic_lower (N M : Real) (hN : 1 < N) (hM : 0 <= M)
    (hMax : M <= (9 / 64 : Real) * (N - 1)) :
    threeLineParityCubicCoefficient * threeLineParityCubicScale N * M ^ 3 <=
      threeLineParityCost N M := by
  have hScale : 0 <= threeLineParityCubicScale N * M ^ 3 :=
    mul_nonneg (le_of_lt (threeLineParityCubicScale_pos N hN)) (pow_nonneg hM 3)
  calc
    _ = (threeLineParityCubicScale N * M ^ 3) * threeLineParityCubicCoefficient := by ring
    _ <= (threeLineParityCubicScale N * M ^ 3) * threeLineParityNormalizedCost N M :=
      _root_.mul_le_mul_of_nonneg_left (threeLineParityNormalizedCost_ge N M hN hM hMax) hScale
    _ = threeLineParityCost N M := (threeLineParityCost_cubic_factorization N M hN hM hMax).symm

theorem threeLineParityCost_cubic_strict (N M : Real) (hN : 1 < N) (hM : 0 < M)
    (hMax : M <= (9 / 64 : Real) * (N - 1)) :
    threeLineParityCubicCoefficient * threeLineParityCubicScale N * M ^ 3 <
      threeLineParityCost N M := by
  have hScale : 0 < threeLineParityCubicScale N * M ^ 3 :=
    mul_pos (threeLineParityCubicScale_pos N hN) (pow_pos hM 3)
  calc
    _ = (threeLineParityCubicScale N * M ^ 3) * threeLineParityCubicCoefficient := by ring
    _ < (threeLineParityCubicScale N * M ^ 3) * threeLineParityNormalizedCost N M :=
      _root_.mul_lt_mul_of_pos_left (threeLineParityNormalizedCost_gt N M hN hM hMax) hScale
    _ = threeLineParityCost N M :=
      (threeLineParityCost_cubic_factorization N M hN (le_of_lt hM) hMax).symm

theorem threeLineParityCost_larger_coefficient_fails (N c : Real) (hN : 1 < N)
    (hc : threeLineParityCubicCoefficient < c) :
    exists M : Real, And (0 < M) (And (M <= (9 / 64 : Real) * (N - 1))
      (threeLineParityCost N M < c * threeLineParityCubicScale N * M ^ 3)) := by
  have hEps : 0 < c - threeLineParityCubicCoefficient := sub_pos.mpr hc
  choose delta hDelta hClose using
    (Metric.continuousAt_iff.mp (threeLineParityNormalizedCost_continuousAt_zero N))
      (c - threeLineParityCubicCoefficient) hEps
  have hMaxPos : 0 < (9 / 64 : Real) * (N - 1) := by
    apply mul_pos (by norm_num)
    linarith
  let M := min delta ((9 / 64 : Real) * (N - 1)) / 2
  have hMinPos : 0 < min delta ((9 / 64 : Real) * (N - 1)) := lt_min hDelta hMaxPos
  have hM : 0 < M := div_pos hMinPos (by norm_num)
  have hLeft := min_le_left delta ((9 / 64 : Real) * (N - 1))
  have hRight := min_le_right delta ((9 / 64 : Real) * (N - 1))
  have hSmall : M < delta := by dsimp only [M]; linarith
  have hMax : M <= (9 / 64 : Real) * (N - 1) := by dsimp only [M]; linarith
  have hDist : dist M 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hM]
    exact hSmall
  have hNear := hClose hDist
  rw [threeLineParityNormalizedCost_zero N hN, Real.dist_eq] at hNear
  have hCost : threeLineParityNormalizedCost N M < c := by
    have hu := (abs_lt.mp hNear).2
    linarith
  have hScale : 0 < threeLineParityCubicScale N * M ^ 3 :=
    mul_pos (threeLineParityCubicScale_pos N hN) (pow_pos hM 3)
  apply Exists.intro M
  apply And.intro hM
  apply And.intro hMax
  rw [threeLineParityCost_cubic_factorization N M hN (le_of_lt hM) hMax]
  calc
    _ < (threeLineParityCubicScale N * M ^ 3) * c :=
      _root_.mul_lt_mul_of_pos_left hCost hScale
    _ = c * threeLineParityCubicScale N * M ^ 3 := by ring

theorem threeLineParityCubicCoefficient_optimal (N c : Real) (hN : 1 < N) :
    (forall M : Real, 0 <= M -> M <= (9 / 64 : Real) * (N - 1) ->
      c * threeLineParityCubicScale N * M ^ 3 <= threeLineParityCost N M) <->
        c <= threeLineParityCubicCoefficient := by
  constructor
  case mp =>
    intro h
    by_contra hc
    have hGreater : threeLineParityCubicCoefficient < c := lt_of_not_ge hc
    choose M hM hMax hFail using threeLineParityCost_larger_coefficient_fails N c hN hGreater
    have hBound := h M (le_of_lt hM) hMax
    linarith
  case mpr =>
    intro hc M hM hMax
    have hScale : 0 <= threeLineParityCubicScale N * M ^ 3 :=
      mul_nonneg (le_of_lt (threeLineParityCubicScale_pos N hN)) (pow_nonneg hM 3)
    calc
      _ = c * (threeLineParityCubicScale N * M ^ 3) := by ring
      _ <= threeLineParityCubicCoefficient * (threeLineParityCubicScale N * M ^ 3) :=
        _root_.mul_le_mul_of_nonneg_right hc hScale
      _ = threeLineParityCubicCoefficient * threeLineParityCubicScale N * M ^ 3 := by ring
      _ <= threeLineParityCost N M := threeLineParityCost_cubic_lower N M hN hM hMax

end PrimeFactorOscillations
