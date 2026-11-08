/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdSingleLevelCost
import PrimeFactorOscillations.Helpers.ThresholdTotalModels

/-! # Optimal single-level linear stability with fixed-mass finite witnesses -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdSingleFamilyHigh (J K d e : Real) : Real :=
  thresholdModelHigh J K (d - e)

def thresholdSingleFamilyGap (J K d e : Real) : Real :=
  J * e - K * (thresholdSingleFamilyHigh J K d e - thresholdModelHigh J K d)

def thresholdSingleFamilyCost (J K d e : Real) : Real :=
  J * e + K * abs (thresholdSingleFamilyHigh J K d e - thresholdModelHigh J K d)


theorem thresholdSingleFamily_root_difference (J K d e : Real)
    (hJ : 0 <= J) (hK : 0 < K) (hd : And (0 < d) (d < 1))
    (he : And (0 <= e) (e <= d)) :
    let v := thresholdModelHigh J K d
    let h := thresholdSingleFamilyHigh J K d e
    And (1 <= v) (And (1 <= h)
      (K * (h - v) * (h + v - 1) = J * e * (2 * d - 1 - e))) := by
  dsimp only
  have hu : And (0 <= d - e) (d - e <= 1) :=
    And.intro (sub_nonneg.mpr he.2) (by linarith only [he.1, hd.2])
  have hv := thresholdModelHigh_bounds J K d hJ hK (And.intro hd.1.le hd.2.le)
  have hh := thresholdModelHigh_bounds J K (d - e) hJ hK hu
  have hV := thresholdModelHigh_moment J K d hJ hK (And.intro hd.1.le hd.2.le)
  have hH := thresholdModelHigh_moment J K (d - e) hJ hK hu
  refine And.intro hv (And.intro hh ?_)
  dsimp only [thresholdSingleFamilyHigh]
  nlinarith only [hV, hH]

theorem thresholdSingleFamily_gap_bounds (J K d e : Real)
    (hJ : 0 < J) (hK : 0 < K) (hd : And (0 < d) (d < 1))
    (he : And (0 < e) (e < d)) :
    And (0 < thresholdSingleFamilyGap J K d e)
      (thresholdSingleFamilyGap J K d e <= 2 * J * e) := by
  let v := thresholdModelHigh J K d
  let h := thresholdSingleFamilyHigh J K d e
  let A := K * (h - v)
  let T := h + v - 1
  have hr := thresholdSingleFamily_root_difference J K d e hJ.le hK hd
    (And.intro he.1.le he.2.le)
  have hT : 1 <= T := by dsimp only [T]; linarith only [hr.1, hr.2.1]
  have hRoot : A * T = J * e * (2 * d - 1 - e) := hr.2.2
  have hIdentity : thresholdSingleFamilyGap J K d e * T =
      J * e * (h + v - 2 * d + e) := by
    change (J * e - A) * T = J * e * (h + v - 2 * d + e)
    dsimp only [T] at *
    nlinarith only [hRoot]
  have hPositive : 0 < J * e * (h + v - 2 * d + e) :=
    mul_pos (mul_pos hJ he.1) (by linarith only [hr.1, hr.2.1, hd.2, he.1])
  have hGap : 0 < thresholdSingleFamilyGap J K d e := by
    by_contra hn
    have hBad := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (le_trans (by norm_num) hT)
    rw [hIdentity] at hBad
    exact (not_le_of_gt hPositive) hBad
  have hLower : -J * e <= A := by
    by_cases hA : 0 <= A
    case pos => nlinarith only [hA, mul_pos hJ he.1]
    case neg =>
      have hCross := mul_nonneg (neg_nonneg.mpr (le_of_not_ge hA)) (sub_nonneg.mpr hT)
      have hAlpha := mul_nonneg (mul_nonneg hJ.le he.1.le)
        (show 0 <= 2 * d - e by linarith only [he.2, hd.1])
      nlinarith only [hRoot, hCross, hAlpha]
  refine And.intro hGap ?_
  change J * e - A <= 2 * J * e
  nlinarith only [hLower]

def thresholdSingleSlopeTest (J K d c e : Real) : Real :=
  J * (1 - c) + (1 + c) * J * (2 * d - 1 - e) /
    (thresholdSingleFamilyHigh J K d e + thresholdModelHigh J K d - 1)

theorem thresholdSingleSlopeTest_zero_pos (J K d c : Real)
    (hJ : 0 < J) (hK : 0 < K) (hd : And (0 < d) (d < 1))
    (hc : c < (thresholdModelHigh J K d + d - 1) / (thresholdModelHigh J K d - d)) :
    0 < thresholdSingleSlopeTest J K d c 0 := by
  let v := thresholdModelHigh J K d
  have hv : 1 <= v := thresholdModelHigh_bounds J K d hJ.le hK
    (And.intro hd.1.le hd.2.le)
  have hVD : 0 < v - d := by linarith only [hv, hd.2]
  have hDen : 0 < 2 * v - 1 := by linarith only [hv]
  have hFormula : thresholdSingleSlopeTest J K d c 0 =
      2 * J * (v - d) * ((v + d - 1) / (v - d) - c) / (2 * v - 1) := by
    dsimp only [thresholdSingleSlopeTest, thresholdSingleFamilyHigh]
    simp only [sub_zero]
    change J * (1 - c) + (1 + c) * J * (2 * d - 1) / (v + v - 1) = _
    rw [show v + v - 1 = 2 * v - 1 by ring]
    field_simp [hVD.ne', hDen.ne']
    ring
  rw [hFormula]
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hJ) hVD) (sub_pos.mpr hc)) hDen

theorem thresholdSingleSlopeTest_continuousAt_zero (J K d c : Real)
    (hJ : 0 <= J) (hK : 0 < K) (hd : And (0 < d) (d < 1)) :
    ContinuousAt (thresholdSingleSlopeTest J K d c) 0 := by
  let v := thresholdModelHigh J K d
  have hv : 1 <= v := thresholdModelHigh_bounds J K d hJ hK
    (And.intro hd.1.le hd.2.le)
  have hHigh : Continuous (thresholdSingleFamilyHigh J K d) := by
    unfold thresholdSingleFamilyHigh thresholdModelHigh
    fun_prop
  have hNum : Continuous (fun e : Real => (1 + c) * J * (2 * d - 1 - e)) := by fun_prop
  have hDen : Continuous (fun e : Real => thresholdSingleFamilyHigh J K d e + v - 1) :=
    (hHigh.add continuous_const).sub continuous_const
  have hZero : thresholdSingleFamilyHigh J K d 0 = v := by
    simp only [thresholdSingleFamilyHigh, sub_zero, v]
  have hNonzero : Not (thresholdSingleFamilyHigh J K d 0 + v - 1 = 0) := by
    rw [hZero]
    linarith only [hv]
  exact continuousAt_const.add (hNum.continuousAt.div hDen.continuousAt hNonzero)

theorem thresholdSingleSlopeTest_near_zero (J K d c : Real)
    (hJ : 0 < J) (hK : 0 < K) (hd : And (0 < d) (d < 1))
    (hc : c < (thresholdModelHigh J K d + d - 1) / (thresholdModelHigh J K d - d)) :
    exists r : Real, And (0 < r) (forall e : Real, abs e < r ->
      0 < thresholdSingleSlopeTest J K d c e) := by
  have hp := thresholdSingleSlopeTest_zero_pos J K d c hJ hK hd hc
  have hCont := thresholdSingleSlopeTest_continuousAt_zero J K d c hJ.le hK hd
  choose r hr hNear using (Metric.continuousAt_iff.mp hCont)
    (thresholdSingleSlopeTest J K d c 0 / 2) (div_pos hp (by norm_num))
  refine Exists.intro r (And.intro hr ?_)
  intro e he
  have hDist := hNear (show dist e 0 < r by simpa only [Real.dist_eq, sub_zero] using he)
  have hAbs : abs (thresholdSingleSlopeTest J K d c e -
      thresholdSingleSlopeTest J K d c 0) < thresholdSingleSlopeTest J K d c 0 / 2 := by
    simpa only [Real.dist_eq] using hDist
  linarith only [(abs_lt.mp hAbs).1, hp]

theorem thresholdSingleFamily_signed_excess (J K d c e : Real)
    (hJ : 0 < J) (hK : 0 < K) (hd : And (0 < d) (d < 1))
    (he : And (0 < e) (e < d)) (hCross : e < 2 * d - 1) :
    thresholdSingleFamilyCost J K d e - c * thresholdSingleFamilyGap J K d e =
      e * thresholdSingleSlopeTest J K d c e := by
  let v := thresholdModelHigh J K d
  let h := thresholdSingleFamilyHigh J K d e
  let T := h + v - 1
  have hr := thresholdSingleFamily_root_difference J K d e hJ.le hK hd
    (And.intro he.1.le he.2.le)
  have hT : 0 < T := by dsimp only [T]; linarith only [hr.1, hr.2.1]
  have hRoot : K * (h - v) * T = J * e * (2 * d - 1 - e) := hr.2.2
  have hDiff : 0 < h - v := by
    have hProd : 0 < K * (h - v) * T := by
      rw [hRoot]
      exact mul_pos (mul_pos hJ he.1) (sub_pos.mpr hCross)
    by_contra hn
    have hBad := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hK.le (le_of_not_gt hn)) hT.le
    exact (not_le_of_gt hProd) hBad
  have hScaled := congrArg (fun q : Real => (1 + c) * q) hRoot
  change J * e + K * abs (h - v) - c * (J * e - K * (h - v)) =
    e * (J * (1 - c) + (1 + c) * J * (2 * d - 1 - e) / T)
  rw [abs_of_nonneg hDiff.le]
  field_simp [hT.ne']
  nlinarith only [hScaled]

theorem thresholdSingleFamily_sharp_above_half (J K d c eta : Real)
    (hJ : 0 < J) (hK : 0 < K) (hd : And (1 / 2 < d) (d < 1)) (hEta : 0 < eta)
    (hc : c < (thresholdModelHigh J K d + d - 1) / (thresholdModelHigh J K d - d)) :
    exists e : Real, And (And (0 < e) (e < d))
      (And (0 < thresholdSingleFamilyGap J K d e)
        (And (thresholdSingleFamilyGap J K d e < eta)
          (c * thresholdSingleFamilyGap J K d e < thresholdSingleFamilyCost J K d e))) := by
  have hd0 : And (0 < d) (d < 1) := And.intro (by linarith only [hd.1]) hd.2
  have hAlpha : 0 < 2 * d - 1 := by linarith only [hd.1]
  choose r hr hNear using thresholdSingleSlopeTest_near_zero J K d c hJ hK hd0 hc
  let e := min (d / 2) (min ((2 * d - 1) / 2) (min (r / 2) (eta / (4 * J))))
  have he0 : 0 < e := lt_min (div_pos hd0.1 (by norm_num))
    (lt_min (div_pos hAlpha (by norm_num))
      (lt_min (div_pos hr (by norm_num)) (div_pos hEta (mul_pos (by norm_num) hJ))))
  have heD : e <= d / 2 := min_le_left _ _
  have heAlpha : e <= (2 * d - 1) / 2 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have heR : e <= r / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have heEta : e <= eta / (4 * J) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have he : And (0 < e) (e < d) := And.intro he0 (by linarith only [heD, hd0.1])
  have hGap := thresholdSingleFamily_gap_bounds J K d e hJ hK hd0 he
  have hG := hNear e (by rw [abs_of_nonneg he0.le]; linarith only [heR, hr])
  have hSigned := thresholdSingleFamily_signed_excess J K d c e hJ hK hd0 he
    (by linarith only [heAlpha, hAlpha])
  have hGain : c * thresholdSingleFamilyGap J K d e < thresholdSingleFamilyCost J K d e := by
    have hp := mul_pos he0 hG
    rw [<- hSigned] at hp
    linarith only [hp]
  have hSmall : thresholdSingleFamilyGap J K d e < eta := by
    have hMul := mul_le_mul_of_nonneg_left heEta
      (mul_nonneg (show (0 : Real) <= 4 by norm_num) hJ.le)
    have hCancel : (4 * J) * (eta / (4 * J)) = eta := by field_simp [hJ.ne']
    rw [hCancel] at hMul
    nlinarith only [hMul, hGap.2, hEta]
  exact Exists.intro e (And.intro he (And.intro hGap.1 (And.intro hSmall hGain)))

theorem thresholdSingleFamily_cost_eq_gap (J K d e : Real)
    (hJ : 0 < J) (hK : 0 < K) (hd : And (0 < d) (d <= 1 / 2))
    (he : And (0 < e) (e < d)) :
    thresholdSingleFamilyCost J K d e = thresholdSingleFamilyGap J K d e := by
  have hd1 : And (0 < d) (d < 1) := And.intro hd.1 (by linarith only [hd.2])
  have hr := thresholdSingleFamily_root_difference J K d e hJ.le hK hd1
    (And.intro he.1.le he.2.le)
  let v := thresholdModelHigh J K d
  let h := thresholdSingleFamilyHigh J K d e
  have hNonpos : h - v <= 0 := by
    by_contra hn
    have hDiff : 0 < h - v := lt_of_not_ge hn
    have hLeft : 0 < K * (h - v) * (h + v - 1) :=
      mul_pos (mul_pos hK hDiff) (by linarith only [hr.1, hr.2.1])
    have hRight : J * e * (2 * d - 1 - e) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hJ he.1) (by linarith only [hd.2, he.1])
    linarith only [hr.2.2, hLeft, hRight]
  change J * e + K * abs (h - v) = J * e - K * (h - v)
  rw [abs_of_nonpos hNonpos]
  ring

theorem thresholdSingleFamily_sharp_at_most_half (J K d c eta : Real)
    (hJ : 0 < J) (hK : 0 < K) (hd : And (0 < d) (d <= 1 / 2))
    (hEta : 0 < eta) (hc : c < 1) :
    exists e : Real, And (And (0 < e) (e < d))
      (And (0 < thresholdSingleFamilyGap J K d e)
        (And (thresholdSingleFamilyGap J K d e < eta)
          (c * thresholdSingleFamilyGap J K d e < thresholdSingleFamilyCost J K d e))) := by
  let e := min (d / 2) (eta / (4 * J))
  have he0 : 0 < e := lt_min (div_pos hd.1 (by norm_num))
    (div_pos hEta (mul_pos (by norm_num) hJ))
  have heD : e <= d / 2 := min_le_left _ _
  have heEta : e <= eta / (4 * J) := min_le_right _ _
  have he : And (0 < e) (e < d) := And.intro he0 (by linarith only [heD, hd.1])
  have hGap := thresholdSingleFamily_gap_bounds J K d e hJ hK
    (And.intro hd.1 (by linarith only [hd.2])) he
  have hSmall : thresholdSingleFamilyGap J K d e < eta := by
    have hMul := mul_le_mul_of_nonneg_left heEta
      (mul_nonneg (show (0 : Real) <= 4 by norm_num) hJ.le)
    have hCancel : (4 * J) * (eta / (4 * J)) = eta := by field_simp [hJ.ne']
    rw [hCancel] at hMul
    nlinarith only [hMul, hGap.2, hEta]
  have hEqual := thresholdSingleFamily_cost_eq_gap J K d e hJ hK hd he
  have hGain : c * thresholdSingleFamilyGap J K d e < thresholdSingleFamilyCost J K d e := by
    rw [hEqual]
    nlinarith only [mul_pos (sub_pos.mpr hc) hGap.1]
  exact Exists.intro e (And.intro he (And.intro hGap.1 (And.intro hSmall hGain)))

theorem thresholdSingleFamily_sharp_coefficient (J K d c eta : Real)
    (hJ : 0 < J) (hK : 0 < K) (hd : And (0 < d) (d < 1)) (hEta : 0 < eta)
    (hc : c < thresholdSingleCoefficient d (thresholdModelHigh J K d)) :
    exists e : Real, And (And (0 < e) (e < d))
      (And (0 < thresholdSingleFamilyGap J K d e)
        (And (thresholdSingleFamilyGap J K d e < eta)
          (c * thresholdSingleFamilyGap J K d e < thresholdSingleFamilyCost J K d e))) := by
  let v := thresholdModelHigh J K d
  have hv : 1 <= v := thresholdModelHigh_bounds J K d hJ.le hK
    (And.intro hd.1.le hd.2.le)
  have hVD : 0 < v - d := by linarith only [hv, hd.2]
  have hCancel : (v + d - 1) / (v - d) * (v - d) = v + d - 1 := by
    field_simp [hVD.ne']
  by_cases hHalf : d <= 1 / 2
  case pos =>
    have hQ : (v + d - 1) / (v - d) <= 1 := by
      by_contra hn
      have hBad := mul_pos hVD (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith only [hBad, hCancel, hHalf]
    have hCoeff : thresholdSingleCoefficient d v = 1 := max_eq_left hQ
    rw [hCoeff] at hc
    exact thresholdSingleFamily_sharp_at_most_half J K d c eta hJ hK
      (And.intro hd.1 hHalf) hEta hc
  case neg =>
    have hQ : 1 <= (v + d - 1) / (v - d) := by
      by_contra hn
      have hBad := mul_pos hVD (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith only [hBad, hCancel, lt_of_not_ge hHalf]
    have hCoeff : thresholdSingleCoefficient d v = (v + d - 1) / (v - d) := max_eq_right hQ
    rw [hCoeff] at hc
    exact thresholdSingleFamily_sharp_above_half J K d c eta hJ hK
      (And.intro (lt_of_not_ge hHalf) hd.2) hEta hc

def thresholdSinglePairWeights (J K : Real) (i : Fin 2) : Real :=
  if i.val = 0 then J else K

theorem thresholdSinglePair_sum (J K u v : Real) (phi : Real -> Real) :
    Finset.sum Finset.univ (fun i => thresholdSinglePairWeights J K i *
      phi (thresholdPairCoords u v i)) = J * phi u + K * phi v := by
  norm_num [Fin.sum_univ_succ, thresholdSinglePairWeights, thresholdPairCoords]

theorem thresholdSinglePair_data (J K d e : Real)
    (hJ : 0 < J) (hK : 0 < K) (hd : And (0 < d) (d < 1))
    (he : And (0 < e) (e < d)) :
    let a := thresholdSinglePairWeights J K
    let y := thresholdPairCoords (d - e) (thresholdSingleFamilyHigh J K d e)
    let M := thresholdTotalUpper d (J + K) K - thresholdSingleFamilyGap J K d e
    And (forall i, 0 <= a i)
      (And (forall i, 0 <= y i)
        (And (Finset.sum Finset.univ a = J + K)
          (And (Finset.sum Finset.univ (fun i => a i * y i) = M)
            (And (Finset.sum Finset.univ (fun i => a i * (y i) ^ 2) = M)
              (thresholdSelectedMass d Finset.univ a y = K))))) := by
  dsimp only
  have hr := thresholdSingleFamily_root_difference J K d e hJ.le hK hd
    (And.intro he.1.le he.2.le)
  have hIlo : momentRoundIndicator d (d - e) = 0 := by
    have hlo : d - e < d := by linarith only [he.1]
    simp only [momentRoundIndicator, ite_eq_right (not_le.mpr hlo)]
  have hIhi : momentRoundIndicator d (thresholdSingleFamilyHigh J K d e) = 1 := by
    simp [momentRoundIndicator, show d <= thresholdSingleFamilyHigh J K d e by
      linarith only [hr.2.1, hd.2]]
  have hFirst : J * (d - e) + K * thresholdSingleFamilyHigh J K d e =
      thresholdTotalUpper d (J + K) K - thresholdSingleFamilyGap J K d e := by
    unfold thresholdTotalUpper thresholdSingleFamilyGap
    rw [show J + K - K = J by ring]
    ring
  have hSecond := thresholdModelHigh_moment J K (d - e) hJ.le hK
    (And.intro (sub_nonneg.mpr he.2.le) (by linarith only [hd.2, he.1]))
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))
  next =>
    intro i
    unfold thresholdSinglePairWeights
    split_ifs <;> linarith only [hJ, hK]
  next =>
    intro i
    unfold thresholdPairCoords
    split_ifs <;> linarith only [he.2, hr.2.1]
  next =>
    simpa only [mul_one] using thresholdSinglePair_sum J K (d - e)
      (thresholdSingleFamilyHigh J K d e) (fun _ => (1 : Real))
  next =>
    rw [thresholdSinglePair_sum J K (d - e) (thresholdSingleFamilyHigh J K d e) (fun z => z)]
    exact hFirst
  next =>
    rw [thresholdSinglePair_sum J K (d - e) (thresholdSingleFamilyHigh J K d e) (fun z => z ^ 2)]
    exact hSecond.trans hFirst
  next =>
    unfold thresholdSelectedMass
    rw [thresholdSinglePair_sum J K (d - e) (thresholdSingleFamilyHigh J K d e)
      (momentRoundIndicator d), hIlo, hIhi]
    ring

theorem thresholdSinglePair_cost (J K d e : Real)
    (hJ : 0 <= J) (hK : 0 < K) (hd : And (0 < d) (d < 1))
    (he : And (0 < e) (e < d)) :
    let v := thresholdModelHigh J K d
    Finset.sum Finset.univ (fun i => thresholdSinglePairWeights J K i *
      abs (thresholdPairCoords (d - e) (thresholdSingleFamilyHigh J K d e) i - v)) -
      thresholdTotalStatistic d v (J + K) K (fun z => abs (z - v)) =
        thresholdSingleFamilyCost J K d e := by
  dsimp only
  have hr := thresholdSingleFamily_root_difference J K d e hJ hK hd
    (And.intro he.1.le he.2.le)
  rw [thresholdSinglePair_sum J K (d - e) (thresholdSingleFamilyHigh J K d e)
    (fun z => abs (z - thresholdModelHigh J K d))]
  unfold thresholdTotalStatistic
  dsimp only
  rw [show J + K - K = J by ring, sub_self, abs_zero, mul_zero, add_zero]
  rw [abs_of_nonpos (show d - e - thresholdModelHigh J K d <= 0 by
    linarith only [hr.1, hd.2, he.1])]
  rw [abs_of_nonpos (show d - thresholdModelHigh J K d <= 0 by
    linarith only [hr.1, hd.2])]
  unfold thresholdSingleFamilyCost
  ring

theorem thresholdSinglePair_sharp (J K d c eta : Real)
    (hJ : 0 < J) (hK : 0 < K) (hd : And (0 < d) (d < 1)) (hEta : 0 < eta)
    (hc : c < thresholdSingleCoefficient d (thresholdModelHigh J K d)) :
    exists e : Real,
      let a := thresholdSinglePairWeights J K
      let y := thresholdPairCoords (d - e) (thresholdSingleFamilyHigh J K d e)
      let v := thresholdModelHigh J K d
      let Delta := thresholdSingleFamilyGap J K d e
      And (And (0 < e) (e < d))
        (And (And (0 < Delta) (Delta < eta))
          (And (Finset.sum Finset.univ a = J + K)
            (And (Finset.sum Finset.univ (fun i => a i * y i) =
                thresholdTotalUpper d (J + K) K - Delta)
              (And (Finset.sum Finset.univ (fun i => a i * (y i) ^ 2) =
                  thresholdTotalUpper d (J + K) K - Delta)
                (And (thresholdSelectedMass d Finset.univ a y = K)
                  (c * Delta < abs (Finset.sum Finset.univ (fun i => a i * abs (y i - v)) -
                    thresholdTotalStatistic d v (J + K) K (fun z => abs (z - v))))))))) := by
  choose e he hGap hSmall hGain using
    thresholdSingleFamily_sharp_coefficient J K d c eta hJ hK hd hEta hc
  have hData := thresholdSinglePair_data J K d e hJ hK hd he
  have hCost := thresholdSinglePair_cost J K d e hJ.le hK hd he
  refine Exists.intro e (And.intro he (And.intro (And.intro hGap hSmall)
    (And.intro hData.2.2.1 (And.intro hData.2.2.2.1
      (And.intro hData.2.2.2.2.1 (And.intro hData.2.2.2.2.2 ?_))))))
  rw [hCost]
  exact lt_of_lt_of_le hGain (le_abs_self _)

theorem finiteEven_minimal_selected_sharp (m : Nat) (d c eta : Real)
    (hm : 0 < m) (hd : And (0 < d) (d < 1)) (hEta : 0 < eta)
    (hc : c < thresholdSingleCoefficient d (thresholdModelHigh (2 * (m : Real)) 2 d)) :
    exists e : Real,
      let a := thresholdPairWeights m 1
      let y := thresholdPairCoords (d - e) (thresholdSingleFamilyHigh (2 * (m : Real)) 2 d e)
      let Delta := thresholdSingleFamilyGap (2 * (m : Real)) 2 d e
      let N := 2 * (m : Real) + 2
      let v := thresholdModelHigh (2 * (m : Real)) 2 d
      And (And (0 < Delta) (Delta < eta))
        (And (thresholdTotalAdmissible d (thresholdTotalUpper d N 2 - Delta) N 2 a y)
          (c * Delta < abs (Finset.sum Finset.univ (fun i => 2 * (a i : Real) *
            abs (y i - v)) - thresholdTotalStatistic d v N 2 (fun z => abs (z - v))))) := by
  have hJ : 0 < 2 * (m : Real) := by exact_mod_cast (show 0 < 2 * m by omega)
  choose e he hGap hSmall hGain using
    thresholdSingleFamily_sharp_coefficient (2 * (m : Real)) 2 d c eta hJ
      (by norm_num) hd hEta hc
  have hData := thresholdSinglePair_data (2 * (m : Real)) 2 d e hJ
    (by norm_num) hd he
  have hWeights : (fun i => 2 * (thresholdPairWeights m 1 i : Real)) =
      thresholdSinglePairWeights (2 * (m : Real)) 2 := by
    funext i
    unfold thresholdPairWeights thresholdSinglePairWeights
    split_ifs <;> norm_num
  have hWeightsAt (i : Fin 2) : 2 * (thresholdPairWeights m 1 i : Real) =
      thresholdSinglePairWeights (2 * (m : Real)) 2 i := congrFun hWeights i
  have hAd : thresholdTotalAdmissible d
      (thresholdTotalUpper d (2 * (m : Real) + 2) 2 -
        thresholdSingleFamilyGap (2 * (m : Real)) 2 d e)
      (2 * (m : Real) + 2) 2 (thresholdPairWeights m 1)
      (thresholdPairCoords (d - e) (thresholdSingleFamilyHigh (2 * (m : Real)) 2 d e)) := by
    unfold thresholdTotalAdmissible thresholdEvenAdmissible
    simp_rw [hWeightsAt]
    exact And.intro hData.2.2.1
      (And.intro hData.2.1 (And.intro hData.2.2.2.1
        (And.intro hData.2.2.2.2.1 hData.2.2.2.2.2)))
  refine Exists.intro e (And.intro (And.intro hGap hSmall) (And.intro hAd ?_))
  simp_rw [hWeightsAt]
  rw [thresholdSinglePair_cost (2 * (m : Real)) 2 d e hJ.le (by norm_num) hd he]
  exact lt_of_lt_of_le hGain (le_abs_self _)

end PrimeFactorOscillations
