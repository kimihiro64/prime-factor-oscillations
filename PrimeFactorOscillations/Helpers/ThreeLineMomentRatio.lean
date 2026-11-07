/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.FiniteWeightedRounding
import PrimeFactorOscillations.Helpers.ThreeLineParityCubic

/-! # Joint second and fourth moments through the signed size-biased profile -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def threeLineSizeBiasedProfile (x : Real) : Real :=
  threeLineWeight1 / (threeLineRadius1 * (threeLineRadius1 ^ 2 - x)) +
    threeLineWeight2 / (threeLineRadius2 * (threeLineRadius2 ^ 2 - x)) +
    threeLineWeight3 / (threeLineRadius3 * (threeLineRadius3 ^ 2 - x))

def threeLineSizeBiasedSlope (z : Real) : Real :=
  threeLineWeight1 / (threeLineRadius1 * (threeLineRadius1 ^ 2 - z) ^ 2) +
    threeLineWeight2 / (threeLineRadius2 * (threeLineRadius2 ^ 2 - z) ^ 2) +
    threeLineWeight3 / (threeLineRadius3 * (threeLineRadius3 ^ 2 - z) ^ 2)

def threeLineSizeBiasedRemainder (x z : Real) : Real :=
  threeLineWeight1 / (threeLineRadius1 * (threeLineRadius1 ^ 2 - x) * (threeLineRadius1 ^ 2 - z) ^ 2) +
    threeLineWeight2 / (threeLineRadius2 * (threeLineRadius2 ^ 2 - x) * (threeLineRadius2 ^ 2 - z) ^ 2) +
    threeLineWeight3 / (threeLineRadius3 * (threeLineRadius3 ^ 2 - x) * (threeLineRadius3 ^ 2 - z) ^ 2)

theorem threeLineMomentRatio_denominators_pos (x : Real) (hx : x <= 1 / 4) :
    And (0 < threeLineRadius1 ^ 2 - x)
      (And (0 < threeLineRadius2 ^ 2 - x) (0 < threeLineRadius3 ^ 2 - x)) := by
  norm_num [threeLineRadius1, threeLineRadius2, threeLineRadius3]
  constructor
  case left => linarith
  case right => constructor <;> linarith

theorem threeLineSizeBiased_one_identity (a x : Real) (ha : Not (a = 0))
    (hx : Not (a ^ 2 - x = 0)) :
    a / (a ^ 2 - x) = 1 / a + x / (a * (a ^ 2 - x)) := by
  field_simp [ha, hx]
  ring

theorem threeLineSizeBiased_identity (x : Real) (hx : x <= 1 / 4) :
    threeLineHorizontalProfile x = threeLineCharge + x * threeLineSizeBiasedProfile x := by
  have hd := threeLineMomentRatio_denominators_pos x hx
  have ha1 : Not (threeLineRadius1 = 0) := by norm_num [threeLineRadius1]
  have ha2 : Not (threeLineRadius2 = 0) := by norm_num [threeLineRadius2]
  have ha3 : Not (threeLineRadius3 = 0) := by norm_num [threeLineRadius3]
  have h1 := congrArg (fun q : Real => threeLineWeight1 * q)
    (threeLineSizeBiased_one_identity threeLineRadius1 x ha1 hd.1.ne')
  have h2 := congrArg (fun q : Real => threeLineWeight2 * q)
    (threeLineSizeBiased_one_identity threeLineRadius2 x ha2 hd.2.1.ne')
  have h3 := congrArg (fun q : Real => threeLineWeight3 * q)
    (threeLineSizeBiased_one_identity threeLineRadius3 x ha3 hd.2.2.ne')
  have hG : threeLineCharge = threeLineWeight1 / threeLineRadius1 +
      threeLineWeight2 / threeLineRadius2 + threeLineWeight3 / threeLineRadius3 := by
    norm_num [threeLineCharge, threeLineWeight1, threeLineWeight2, threeLineWeight3,
      threeLineRadius1, threeLineRadius2, threeLineRadius3]
  rw [hG]
  unfold threeLineHorizontalProfile threeLineSizeBiasedProfile
  simp only [div_eq_mul_inv] at h1 h2 h3
  simp only [div_eq_mul_inv]
  nlinarith only [h1, h2, h3]

theorem threeLineSizeBiased_one_tangent (a x z : Real) (ha : Not (a = 0))
    (hx : Not (a ^ 2 - x = 0)) (hz : Not (a ^ 2 - z = 0)) :
    1 / (a * (a ^ 2 - x)) - 1 / (a * (a ^ 2 - z)) -
      (x - z) / (a * (a ^ 2 - z) ^ 2) =
        (x - z) ^ 2 / (a * (a ^ 2 - x) * (a ^ 2 - z) ^ 2) := by
  field_simp [ha, hx, hz]
  ring

theorem threeLineSizeBiased_tangent_identity (x z : Real)
    (hx : x <= 1 / 4) (hz : z <= 1 / 4) :
    threeLineSizeBiasedProfile x - threeLineSizeBiasedProfile z -
      threeLineSizeBiasedSlope z * (x - z) =
        threeLineSizeBiasedRemainder x z * (x - z) ^ 2 := by
  have hxd := threeLineMomentRatio_denominators_pos x hx
  have hzd := threeLineMomentRatio_denominators_pos z hz
  have ha1 : Not (threeLineRadius1 = 0) := by norm_num [threeLineRadius1]
  have ha2 : Not (threeLineRadius2 = 0) := by norm_num [threeLineRadius2]
  have ha3 : Not (threeLineRadius3 = 0) := by norm_num [threeLineRadius3]
  have h1 := congrArg (fun q : Real => threeLineWeight1 * q)
    (threeLineSizeBiased_one_tangent threeLineRadius1 x z ha1 hxd.1.ne' hzd.1.ne')
  have h2 := congrArg (fun q : Real => threeLineWeight2 * q)
    (threeLineSizeBiased_one_tangent threeLineRadius2 x z ha2 hxd.2.1.ne' hzd.2.1.ne')
  have h3 := congrArg (fun q : Real => threeLineWeight3 * q)
    (threeLineSizeBiased_one_tangent threeLineRadius3 x z ha3 hxd.2.2.ne' hzd.2.2.ne')
  unfold threeLineSizeBiasedProfile threeLineSizeBiasedSlope threeLineSizeBiasedRemainder
  simp only [div_eq_mul_inv] at h1 h2 h3
  simp only [div_eq_mul_inv]
  nlinarith only [h1, h2, h3]

theorem threeLineSizeBiasedRemainder_gt_one (x z : Real)
    (hx : And (0 <= x) (x <= 1 / 4)) (hz : And (0 <= z) (z <= 1 / 4)) :
    1 < threeLineSizeBiasedRemainder x z := by
  have hxd := threeLineMomentRatio_denominators_pos x hx.2
  have hzd := threeLineMomentRatio_denominators_pos z hz.2
  have h1x := hxd.1
  have h2x := hxd.2.1
  have h3x := hxd.2.2
  have h1z := hzd.1
  have h2z := hzd.2.1
  have h3z := hzd.2.2
  have ha1 : 0 < threeLineRadius1 := by norm_num [threeLineRadius1]
  have ha2 : 0 < threeLineRadius2 := by norm_num [threeLineRadius2]
  have ha3 : 0 < threeLineRadius3 := by norm_num [threeLineRadius3]
  let d1 := threeLineRadius1 * (threeLineRadius1 ^ 2 - x) * (threeLineRadius1 ^ 2 - z) ^ 2
  let d2 := threeLineRadius2 * (threeLineRadius2 ^ 2 - x) * (threeLineRadius2 ^ 2 - z) ^ 2
  let d3 := threeLineRadius3 * (threeLineRadius3 ^ 2 - x) * (threeLineRadius3 ^ 2 - z) ^ 2
  have hd1 : 0 < d1 := mul_pos (mul_pos ha1 h1x) (pow_pos h1z 2)
  have hd2 : 0 < d2 := mul_pos (mul_pos ha2 h2x) (pow_pos h2z 2)
  have hd3 : 0 < d3 := mul_pos (mul_pos ha3 h3x) (pow_pos h3z 2)
  have ha12 : threeLineRadius1 <= threeLineRadius2 := by
    norm_num [threeLineRadius1, threeLineRadius2]
  have hx12 : threeLineRadius1 ^ 2 - x <= threeLineRadius2 ^ 2 - x := by
    norm_num [threeLineRadius1, threeLineRadius2]
  have hz12 : threeLineRadius1 ^ 2 - z <= threeLineRadius2 ^ 2 - z := by
    norm_num [threeLineRadius1, threeLineRadius2]
  have hzSq : (threeLineRadius1 ^ 2 - z) ^ 2 <= (threeLineRadius2 ^ 2 - z) ^ 2 := by
    have h := mul_le_mul hz12 hz12 (le_of_lt h1z) (le_of_lt h2z)
    nlinarith only [h]
  have hd12 : d1 <= d2 :=
    mul_le_mul (mul_le_mul ha12 hx12 (le_of_lt h1x) (le_of_lt ha2)) hzSq
      (sq_nonneg _) (le_of_lt (mul_pos ha2 h2x))
  have h2xBound : threeLineRadius2 ^ 2 - x <= threeLineRadius2 ^ 2 := by linarith [hx.1]
  have h2zBound : threeLineRadius2 ^ 2 - z <= threeLineRadius2 ^ 2 := by linarith [hz.1]
  have h2zSq : (threeLineRadius2 ^ 2 - z) ^ 2 <= threeLineRadius2 ^ 4 := by
    have h := mul_le_mul h2zBound h2zBound (le_of_lt h2z) (sq_nonneg threeLineRadius2)
    nlinarith only [h]
  have hd2Bound : d2 <= threeLineRadius2 ^ 7 := by
    have h := mul_le_mul (_root_.mul_le_mul_of_nonneg_left h2xBound (le_of_lt ha2)) h2zSq
      (sq_nonneg _) (mul_nonneg (le_of_lt ha2) (sq_nonneg threeLineRadius2))
    dsimp only [d2]
    nlinarith only [h]
  have hMargin : threeLineRadius2 ^ 7 < threeLineWeight1 + threeLineWeight2 := by
    norm_num [threeLineRadius2, threeLineWeight1, threeLineWeight2]
  have hc1 : 0 < threeLineWeight1 := by norm_num [threeLineWeight1]
  have hc3 : 0 < threeLineWeight3 := by norm_num [threeLineWeight3]
  have hNum : 0 < threeLineWeight1 * d2 + threeLineWeight2 * d1 - d1 * d2 := by
    have hPos := mul_pos (show 0 < threeLineWeight1 + threeLineWeight2 - d2 by linarith) hd1
    have hDelta := mul_nonneg (le_of_lt hc1) (sub_nonneg.mpr hd12)
    nlinarith
  have hEq : (threeLineWeight1 / d1 + threeLineWeight2 / d2 - 1) * (d1 * d2) =
      threeLineWeight1 * d2 + threeLineWeight2 * d1 - d1 * d2 := by
    field_simp [hd1.ne', hd2.ne']
  have hPair : 1 < threeLineWeight1 / d1 + threeLineWeight2 / d2 := by
    by_contra h
    have hNonpos := mul_nonpos_of_nonpos_of_nonneg
      (show threeLineWeight1 / d1 + threeLineWeight2 / d2 - 1 <= 0 by linarith)
      (le_of_lt (mul_pos hd1 hd2))
    rw [hEq] at hNonpos
    linarith
  change 1 < threeLineWeight1 / d1 + threeLineWeight2 / d2 + threeLineWeight3 / d3
  linarith [div_pos hc3 hd3]

theorem threeLineSizeBiased_strong_tangent (x z : Real)
    (hx : And (0 <= x) (x <= 1 / 4)) (hz : And (0 <= z) (z <= 1 / 4)) :
    threeLineSizeBiasedProfile z + threeLineSizeBiasedSlope z * (x - z) + (x - z) ^ 2 <=
      threeLineSizeBiasedProfile x := by
  have hId := threeLineSizeBiased_tangent_identity x z hx.2 hz.2
  have hPos := mul_nonneg (sub_nonneg.mpr (le_of_lt (threeLineSizeBiasedRemainder_gt_one x z hx hz)))
    (sq_nonneg (x - z))
  nlinarith

def threeLineMomentRatioCharge (N M Q : Real) : Real :=
  threeLineCharge * N + M * threeLineSizeBiasedProfile (Q / M)

theorem finiteWeightedTangentLedger {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (F G z : Real) :
    Finset.sum S (fun i => a i * x i * (F + G * (x i - z) + (x i - z) ^ 2)) =
      F * Finset.sum S (fun i => a i * x i) +
        G * (Finset.sum S (fun i => a i * (x i) ^ 2) - z * Finset.sum S (fun i => a i * x i)) +
          Finset.sum S (fun i => a i * x i * (x i - z) ^ 2) := by
  calc
    _ = Finset.sum S (fun i => (F * (a i * x i) + G * (a i * (x i) ^ 2)) -
        (G * z) * (a i * x i) + a i * x i * (x i - z) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        <- Finset.mul_sum, <- Finset.mul_sum, <- Finset.mul_sum]
      ring

theorem threeLineMomentRatio_phi_ledger {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (hx : forall i, Membership.mem S i -> x i <= 1 / 4) :
    Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) =
      threeLineCharge * Finset.sum S a +
        Finset.sum S (fun i => a i * x i * threeLineSizeBiasedProfile (x i)) := by
  calc
    _ = Finset.sum S (fun i => threeLineCharge * a i +
        a i * x i * threeLineSizeBiasedProfile (x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [threeLineSizeBiased_identity (x i) (hx i hi)]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, <- Finset.mul_sum]

theorem threeLineMomentRatio_energy_nonneg {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> 0 <= x i) :
    0 <= Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (mul_nonneg (ha i hi) (hx i hi)) (sq_nonneg _))

theorem threeLineMomentRatio_weighted_charge {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (ht : And (0 <= t) (t <= 1 / 4))
    (hCenter : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i)) :
    threeLineCharge * Finset.sum S a +
      Finset.sum S (fun i => a i * x i) * threeLineSizeBiasedProfile t +
        Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) <=
      Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) := by
  have hLocal : Finset.sum S (fun i => a i * x i *
      (threeLineSizeBiasedProfile t + threeLineSizeBiasedSlope t * (x i - t) + (x i - t) ^ 2)) <=
        Finset.sum S (fun i => a i * x i * threeLineSizeBiasedProfile (x i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact _root_.mul_le_mul_of_nonneg_left (threeLineSizeBiased_strong_tangent (x i) t (hx i hi) ht)
      (mul_nonneg (ha i hi) (hx i hi).1)
  have hLedger := finiteWeightedTangentLedger S a x (threeLineSizeBiasedProfile t)
    (threeLineSizeBiasedSlope t) t
  rw [hCenter, sub_self, mul_zero, add_zero] at hLedger
  rw [hLedger] at hLocal
  rw [threeLineMomentRatio_phi_ledger S a x (fun i hi => (hx i hi).2)]
  linarith

theorem threeLineMomentRatio_mean_bounds {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hN : 0 < Finset.sum S a) (hM : 0 < Finset.sum S (fun i => a i * x i)) :
    And (0 < Finset.sum S (fun i => a i * (x i) ^ 2))
      (And (0 < Finset.sum S (fun i => a i * (x i) ^ 2) /
        Finset.sum S (fun i => a i * x i))
        (Finset.sum S (fun i => a i * (x i) ^ 2) /
          Finset.sum S (fun i => a i * x i) <= 1 / 4)) := by
  have hSquare := finiteWeightedSquareSum_le S a x ha hN
  have hQ : 0 < Finset.sum S (fun i => a i * (x i) ^ 2) := by
    by_contra h
    have hNonpos := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hN) (le_of_not_gt h)
    have hM2 := pow_pos hM 2
    nlinarith
  have hQMax : Finset.sum S (fun i => a i * (x i) ^ 2) <=
      (1 / 4) * Finset.sum S (fun i => a i * x i) := by
    calc
      _ <= Finset.sum S (fun i => (1 / 4 : Real) * (a i * x i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := mul_nonneg (ha i hi)
          (mul_nonneg (hx i hi).1 (sub_nonneg.mpr (hx i hi).2))
        nlinarith only [h]
      _ = _ := by rw [<- Finset.mul_sum]
  have hMax : Finset.sum S (fun i => a i * (x i) ^ 2) /
      Finset.sum S (fun i => a i * x i) <= 1 / 4 := by
    apply (_root_.mul_le_mul_iff_of_pos_left hM).mp
    have hBalance : Finset.sum S (fun i => a i * x i) *
        (Finset.sum S (fun i => a i * (x i) ^ 2) / Finset.sum S (fun i => a i * x i)) =
          Finset.sum S (fun i => a i * (x i) ^ 2) := by field_simp [hM.ne']
    rw [hBalance]
    linarith
  exact And.intro hQ (And.intro (div_pos hQ hM) hMax)

theorem threeLineMomentRatio_equality_iff {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (ht : And (0 <= t) (t <= 1 / 4))
    (hCenter : Finset.sum S (fun i => a i * (x i) ^ 2) = t * Finset.sum S (fun i => a i * x i)) :
    Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) =
      threeLineCharge * Finset.sum S a +
        Finset.sum S (fun i => a i * x i) * threeLineSizeBiasedProfile t <->
      forall i, Membership.mem S i -> 0 < a i -> 0 < x i -> x i = t := by
  constructor
  case mp =>
    intro hEq i hi haPos hxPos
    have hFull := threeLineMomentRatio_weighted_charge S a x t ha hx ht hCenter
    have hEnergy : Finset.sum S (fun j => a j * x j * (x j - t) ^ 2) <= 0 := by linarith
    have hSingle := Finset.single_le_sum
      (fun j hj => mul_nonneg (mul_nonneg (ha j hj) (hx j hj).1) (sq_nonneg (x j - t))) hi
    by_contra hNe
    have hDiff : Not (x i - t = 0) := by intro h; exact hNe (sub_eq_zero.mp h)
    have hSq : 0 < (x i - t) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hDiff))
    have hPos := mul_pos (mul_pos haPos hxPos) hSq
    linarith
  case mpr =>
    intro hSupport
    have hPoint (i : Iota) (hi : Membership.mem S i) :
        a i * threeLineHorizontalProfile (x i) =
          threeLineCharge * a i + threeLineSizeBiasedProfile t * (a i * x i) := by
      by_cases haZero : a i = 0
      case pos => simp [haZero]
      case neg =>
        by_cases hxZero : x i = 0
        case pos => rw [hxZero, threeLineHorizontalProfile_zero]; ring
        case neg =>
          have hX := hSupport i hi (lt_of_le_of_ne (ha i hi) (Ne.symm haZero))
            (lt_of_le_of_ne (hx i hi).1 (Ne.symm hxZero))
          rw [hX, threeLineSizeBiased_identity t ht.2]
          ring
    calc
      _ = Finset.sum S (fun i => threeLineCharge * a i +
          threeLineSizeBiasedProfile t * (a i * x i)) := Finset.sum_congr rfl hPoint
      _ = threeLineCharge * Finset.sum S a +
          threeLineSizeBiasedProfile t * Finset.sum S (fun i => a i * x i) := by
        rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
      _ = _ := by ring

theorem threeLineMomentRatio_rounding_charge {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hMax : t <= 1 / 4) (hN : 0 < Finset.sum S a)
    (hCenter : Finset.sum S (fun i => a i * (x i) ^ 2) = t * Finset.sum S (fun i => a i * x i)) :
    t ^ 3 * (Finset.sum S (fun i => a i * x i) / t -
      Finset.sum S (fun i => a i * halfRoundIndicator (x i / t))) ^ 2 <=
      2 * Finset.sum S a *
        (Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) -
          (threeLineCharge * Finset.sum S a +
            Finset.sum S (fun i => a i * x i) * threeLineSizeBiasedProfile t)) := by
  have hStrong := threeLineMomentRatio_weighted_charge S a x t ha hx
    (And.intro (le_of_lt ht) hMax) hCenter
  have hRound := finiteWeightedRound_scaled S a x t ht ha (fun i hi => (hx i hi).1) hN
  have hEnergy : Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) <=
      Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) -
        (threeLineCharge * Finset.sum S a +
          Finset.sum S (fun i => a i * x i) * threeLineSizeBiasedProfile t) := by linarith
  have hTransfer := _root_.mul_le_mul_of_nonneg_left hEnergy
    (show 0 <= 2 * Finset.sum S a by linarith)
  exact hRound.trans hTransfer

theorem threeLineSizeBiased_cubic_identity (x : Real) (hx : x <= 9 / 64) :
    threeLineSizeBiasedProfile x = threeLineHorizontalSlope 0 +
      threeLineHorizontalVarianceCoefficient * x + x ^ 2 * threeLineHorizontalCubicTail x := by
  by_cases hxZero : x = 0
  case pos =>
    rw [hxZero]
    norm_num [threeLineSizeBiasedProfile, threeLineHorizontalSlope,
      threeLineWeight1, threeLineWeight2, threeLineWeight3,
      threeLineRadius1, threeLineRadius2, threeLineRadius3]
  case neg =>
    have hCubic := threeLineHorizontal_cubic_identity x hx
    have hBias := threeLineSizeBiased_identity x (by linarith)
    have hProduct : x * (threeLineSizeBiasedProfile x -
        (threeLineHorizontalSlope 0 + threeLineHorizontalVarianceCoefficient * x +
          x ^ 2 * threeLineHorizontalCubicTail x)) = 0 := by
      nlinarith only [hCubic, hBias]
    have hZero := (mul_eq_zero.mp hProduct).resolve_left hxZero
    exact sub_eq_zero.mp hZero

theorem threeLineMomentRatio_two_atom_model (N M Q : Real)
    (hM : 0 < M) (hQ : 0 < Q) (hFeasible : M ^ 2 <= N * Q)
    (hMax : Q <= (1 / 4 : Real) * M) :
    And (0 <= N - M ^ 2 / Q)
      (And (0 < M ^ 2 / Q)
        (And ((M ^ 2 / Q) * (Q / M) = M)
          (And ((M ^ 2 / Q) * (Q / M) ^ 2 = Q)
            ((N - M ^ 2 / Q) * threeLineHorizontalProfile 0 +
              (M ^ 2 / Q) * threeLineHorizontalProfile (Q / M) =
                threeLineMomentRatioCharge N M Q)))) := by
  have hK : 0 < M ^ 2 / Q := div_pos (pow_pos hM 2) hQ
  have hQBalance : Q * (M ^ 2 / Q) = M ^ 2 := by field_simp [hQ.ne']
  have hKN : M ^ 2 / Q <= N := by
    apply (_root_.mul_le_mul_iff_of_pos_left hQ).mp
    rw [hQBalance]
    nlinarith
  have hKM : (M ^ 2 / Q) * (Q / M) = M := by field_simp [hQ.ne', hM.ne']
  have hKQ : (M ^ 2 / Q) * (Q / M) ^ 2 = Q := by field_simp [hQ.ne', hM.ne']
  have hT : Q / M <= 1 / 4 := by
    apply (_root_.mul_le_mul_iff_of_pos_left hM).mp
    have hBalance : M * (Q / M) = Q := by field_simp [hM.ne']
    rw [hBalance]
    linarith
  have hCharge : (N - M ^ 2 / Q) * threeLineHorizontalProfile 0 +
      (M ^ 2 / Q) * threeLineHorizontalProfile (Q / M) = threeLineMomentRatioCharge N M Q := by
    rw [threeLineHorizontalProfile_zero, threeLineSizeBiased_identity (Q / M) hT]
    unfold threeLineMomentRatioCharge
    calc
      _ = threeLineCharge * N + ((M ^ 2 / Q) * (Q / M)) * threeLineSizeBiasedProfile (Q / M) := by ring
      _ = _ := by rw [hKM]
  exact And.intro (sub_nonneg.mpr hKN) (And.intro hK (And.intro hKM (And.intro hKQ hCharge)))

theorem threeLineMomentRatio_residual_comparison (N L M Q : Real)
    (hL : 0 < L) (hM : 0 < M) (hFeasible : M ^ 2 <= L * Q)
    (hMax : Q / M <= 9 / 64) :
    And (threeLineHorizontalVarianceCoefficient * Q + (N - L) * threeLineCharge +
      L * threeLineHorizontalResidualProfile (M / L) <= threeLineMomentRatioCharge N M Q)
      (M ^ 2 < L * Q -> threeLineHorizontalVarianceCoefficient * Q + (N - L) * threeLineCharge +
        L * threeLineHorizontalResidualProfile (M / L) < threeLineMomentRatioCharge N M Q) := by
  let r := M / L
  let t := Q / M
  have hr : 0 < r := div_pos hM hL
  have hRScale : (L * M) * r = M ^ 2 := by dsimp only [r]; field_simp [hL.ne'] <;> ring
  have hTScale : (L * M) * t = L * Q := by dsimp only [t]; field_simp [hM.ne'] <;> ring
  have hOrder : r <= t := by
    apply (_root_.mul_le_mul_iff_of_pos_left (mul_pos hL hM)).mp
    rw [hRScale, hTScale]
    exact hFeasible
  have ht : 0 <= t := le_trans (le_of_lt hr) hOrder
  have htMax : t <= 9 / 64 := hMax
  have hrMax : r <= 9 / 64 := hOrder.trans htMax
  have hLower := threeLineHorizontalCubicTail_mono 0 r (le_of_lt hr) (by norm_num) hrMax
  rw [threeLineHorizontalCubicTail_zero] at hLower
  have hRPos : 0 < threeLineHorizontalCubicTail r :=
    lt_of_lt_of_le threeLineParityCubicCoefficient_pos hLower
  have hMono := threeLineHorizontalCubicTail_mono r t hOrder hrMax htMax
  have hRB : L * r = M := by dsimp only [r]; field_simp [hL.ne']
  have hTB : M * t = Q := by dsimp only [t]; field_simp [hM.ne']
  have hLinear := congrArg (fun q : Real => threeLineHorizontalSlope 0 * q) hRB
  have hCubic := congrArg (fun q : Real => q * r ^ 2 * threeLineHorizontalCubicTail r) hRB
  have hSigma := congrArg (fun q : Real => threeLineHorizontalVarianceCoefficient * q) hTB
  have hDifference : threeLineMomentRatioCharge N M Q -
      (threeLineHorizontalVarianceCoefficient * Q + (N - L) * threeLineCharge +
        L * threeLineHorizontalResidualProfile r) =
      M * ((t ^ 2 - r ^ 2) * threeLineHorizontalCubicTail r +
        t ^ 2 * (threeLineHorizontalCubicTail t - threeLineHorizontalCubicTail r)) := by
    unfold threeLineMomentRatioCharge
    change _ + M * threeLineSizeBiasedProfile t - _ = _
    rw [threeLineSizeBiased_cubic_identity t htMax, threeLineHorizontalResidual_cubic_identity r hrMax]
    nlinarith only [hLinear, hCubic, hSigma]
  have hSq : 0 <= t ^ 2 - r ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hOrder) (show 0 <= t + r by linarith)
    nlinarith only [h]
  have hFirst := mul_nonneg hSq (le_of_lt hRPos)
  have hSecond := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hMono)
  have hDiffNonneg := mul_nonneg (le_of_lt hM) (add_nonneg hFirst hSecond)
  constructor
  case left => change _ <= _; linarith only [hDifference, hDiffNonneg]
  case right =>
    intro hStrict
    have hNe : Not (r = t) := by
      intro h
      rw [h] at hRScale
      linarith only [hRScale, hTScale, hStrict]
    have hRT : r < t := lt_of_le_of_ne hOrder hNe
    have hSqPos : 0 < t ^ 2 - r ^ 2 := by
      have h := mul_pos (sub_pos.mpr hRT) (show 0 < t + r by linarith)
      nlinarith only [h]
    have hFirstPos := mul_pos hSqPos hRPos
    have hTotalPos := mul_pos hM (add_pos_of_pos_of_nonneg hFirstPos hSecond)
    change _ < _
    linarith only [hDifference, hTotalPos]

end PrimeFactorOscillations
