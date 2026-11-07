/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdBandIntegerCost

/-! # Coupled negative threshold packets with an upper cluster readout -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def negativeThresholdHigh (d z : Real) : Real := (d + z) / 2

def negativeThresholdSlope (d z : Real) : Real := (z - d) ^ 2 / 4

def negativeThresholdCurvature (d z : Real) : Real := (z - d) / 2

theorem negativeThreshold_constants (d z : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) :
    And (0 < negativeThresholdSlope d z) (And (0 < negativeThresholdCurvature d z) (d < negativeThresholdHigh d z)) := by
  have hg : 0 < z - d := by linarith only [hd.2, hz]
  unfold negativeThresholdSlope negativeThresholdCurvature negativeThresholdHigh
  exact And.intro (div_pos (sq_pos_of_pos hg) (by norm_num))
    (And.intro (div_pos hg (by norm_num)) (by linarith only [hg]))

theorem negativeThreshold_low_coercivity (d z y : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) (hy : 0 <= y)
    (hLow : y < negativeThresholdHigh d z) :
    negativeThresholdSlope d z * (y - d * momentRoundIndicator d y) <= thresholdNegativePacket d z y := by
  by_cases hCut : d <= y
  case pos =>
    have hFirst : 0 <= z - y - (z - d) / 2 := by dsimp [negativeThresholdHigh] at hLow; linarith only [hLow]
    have hSecond : 0 <= z - y + (z - d) / 2 := by
      dsimp [negativeThresholdHigh] at hLow
      linarith only [hLow, hz, hd.2]
    have hp := mul_nonneg hFirst hSecond
    have hSq : negativeThresholdSlope d z <= (y - z) ^ 2 := by
      unfold negativeThresholdSlope
      nlinarith only [hp]
    have hm := mul_le_mul_of_nonneg_right hSq (sub_nonneg.mpr hCut)
    rw [thresholdNegativePacket_selected d z y hCut]
    simp only [momentRoundIndicator, if_pos hCut, mul_one]
    nlinarith only [hm]
  case neg =>
    have hY : y < d := lt_of_not_ge hCut
    have hp := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hY.le)
      (show y - 2 * z <= 0 by linarith only [hY, hz, hd.2])
    have hA : negativeThresholdSlope d z <= z ^ 2 := by
      have hh := mul_nonneg hd.1.le (show 0 <= 2 * z - d by linarith only [hz, hd.2])
      unfold negativeThresholdSlope
      nlinarith only [hh, sq_nonneg z]
    have hm := mul_nonneg hy hp
    have hm' := mul_nonneg hy (sub_nonneg.mpr hA)
    rw [thresholdNegativePacket_unselected d z y hY]
    simp only [momentRoundIndicator, if_neg hCut, mul_zero, sub_zero]
    nlinarith only [hm, hm']

theorem negativeThreshold_high_coercivity (d z y : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) (hHigh : negativeThresholdHigh d z <= y) :
    negativeThresholdCurvature d z * (y - z) ^ 2 <= thresholdNegativePacket d z y := by
  have hCut : d <= y := le_trans (negativeThreshold_constants d z hd hz).2.2.le hHigh
  rw [thresholdNegativePacket_selected d z y hCut]
  have hMargin : 0 <= y - d - negativeThresholdCurvature d z := by
    dsimp [negativeThresholdHigh] at hHigh
    dsimp [negativeThresholdCurvature]
    linarith only [hHigh]
  have hm := mul_nonneg hMargin (sq_nonneg (y - z))
  nlinarith only [hm]

theorem negativeThreshold_tilted_packet (d z y l s : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) (hy : 0 <= y)
    (hl : And (0 <= l) (l <= negativeThresholdSlope d z)) (hs : Or (s = 1) (s = -1)) :
    0 <= thresholdNegativePacket d z y + l ^ 2 / (4 * negativeThresholdCurvature d z) *
      momentRoundIndicator (negativeThresholdHigh d z) y -
      l * s * (y - d * momentRoundIndicator d y - (z - d) * momentRoundIndicator (negativeThresholdHigh d z) y) := by
  have hc := negativeThreshold_constants d z hd hz
  by_cases hHigh : negativeThresholdHigh d z <= y
  case pos =>
    have hCut : d <= y := le_trans hc.2.2.le hHigh
    have hIh : momentRoundIndicator (negativeThresholdHigh d z) y = 1 := if_pos hHigh
    have hId : momentRoundIndicator d y = 1 := if_pos hCut
    rw [hIh, hId]
    simp only [mul_one]
    have hResidual : y - d - (z - d) = y - z := by ring
    rw [hResidual]
    have hQ := negativeThreshold_high_coercivity d z y hd hz hHigh
    have hIdentity : negativeThresholdCurvature d z * (y - z) ^ 2 +
        l ^ 2 / (4 * negativeThresholdCurvature d z) - l * s * (y - z) =
        (negativeThresholdCurvature d z * (y - z) - l * s / 2) ^ 2 / negativeThresholdCurvature d z := by
      rcases hs with h | h <;> rw [h] <;> field_simp [hc.2.1.ne'] <;> ring
    have hSq := div_nonneg (sq_nonneg (negativeThresholdCurvature d z * (y - z) - l * s / 2)) hc.2.1.le
    linarith only [hQ, hIdentity, hSq]
  case neg =>
    have hIh : momentRoundIndicator (negativeThresholdHigh d z) y = 0 := if_neg hHigh
    rw [hIh]
    simp only [mul_zero, add_zero, sub_zero]
    have hQ := negativeThreshold_low_coercivity d z y hd hz hy (lt_of_not_ge hHigh)
    have hR := thresholdIndicator_defect_nonneg d y hy
    have hSlack := mul_nonneg (sub_nonneg.mpr hl.2) hR
    have hLR := mul_nonneg hl.1 hR
    rcases hs with h | h <;> rw [h] <;> nlinarith only [hQ, hSlack, hLR]

theorem finiteWeightedThreshold_cutoff_antitone {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d h : Real) (hdh : d <= h)
    (ha : forall i, Membership.mem S i -> 0 <= a i) :
    thresholdSelectedMass h S a y <= thresholdSelectedMass d S a y := by
  unfold thresholdSelectedMass
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (ha i hi)
  by_cases hh : h <= y i
  case pos => simp [momentRoundIndicator, hh, le_trans hdh hh]
  case neg =>
    have hI : momentRoundIndicator h (y i) = 0 := if_neg hh
    rw [hI]
    exact thresholdIndicator_nonneg d (y i)

theorem finiteWeightedNegative_joint_tilt {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d z l : Real) (hd : And (0 < d) (d < 1)) (hz : 1 <= z)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hl : And (0 <= l) (l <= negativeThresholdSlope d z)) :
    l * abs (Finset.sum S (fun i => a i * y i) - d * thresholdSelectedMass d S a y -
      (z - d) * thresholdSelectedMass (negativeThresholdHigh d z) S a y) <=
      Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i)) +
        (thresholdSelectedMass (negativeThresholdHigh d z) S a y / negativeThresholdCurvature d z) * l ^ 2 / 4 := by
  have hSigned : forall s : Real, Or (s = 1) (s = -1) ->
      l * s * (Finset.sum S (fun i => a i * y i) - d * thresholdSelectedMass d S a y -
        (z - d) * thresholdSelectedMass (negativeThresholdHigh d z) S a y) <=
      Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i)) +
        (thresholdSelectedMass (negativeThresholdHigh d z) S a y / negativeThresholdCurvature d z) * l ^ 2 / 4 := by
    intro s hs
    have hSum := Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi)
      (negativeThreshold_tilted_packet d z (y i) l s hd hz (hy i hi) hl hs))
    have hIdentity : Finset.sum S (fun i => a i * (thresholdNegativePacket d z (y i) +
        l ^ 2 / (4 * negativeThresholdCurvature d z) * momentRoundIndicator (negativeThresholdHigh d z) (y i) -
        l * s * (y i - d * momentRoundIndicator d (y i) -
          (z - d) * momentRoundIndicator (negativeThresholdHigh d z) (y i)))) =
      Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i)) +
        (thresholdSelectedMass (negativeThresholdHigh d z) S a y / negativeThresholdCurvature d z) * l ^ 2 / 4 -
        l * s * (Finset.sum S (fun i => a i * y i) - d * thresholdSelectedMass d S a y -
          (z - d) * thresholdSelectedMass (negativeThresholdHigh d z) S a y) := by
      calc
        _ = Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i) +
            (l ^ 2 / (4 * negativeThresholdCurvature d z)) *
              (a i * momentRoundIndicator (negativeThresholdHigh d z) (y i)) -
            (l * s) * (a i * y i) + (l * s * d) * (a i * momentRoundIndicator d (y i)) +
            (l * s * (z - d)) * (a i * momentRoundIndicator (negativeThresholdHigh d z) (y i))) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          unfold thresholdSelectedMass
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]
          ring
    rw [hIdentity] at hSum
    linarith only [hSum]
  by_cases h : 0 <= Finset.sum S (fun i => a i * y i) - d * thresholdSelectedMass d S a y -
      (z - d) * thresholdSelectedMass (negativeThresholdHigh d z) S a y
  case pos =>
    rw [abs_of_nonneg h]
    simpa only [mul_one] using hSigned 1 (Or.inl rfl)
  case neg =>
    rw [abs_of_nonpos (le_of_lt (lt_of_not_ge h))]
    have hh := hSigned (-1) (Or.inr rfl)
    nlinarith only [hh]

theorem finiteWeightedNegative_joint_budget {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d z l : Real) (hd : And (0 < d) (d < 1)) (hz : 1 <= z)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hl : And (0 <= l) (l <= negativeThresholdSlope d z)) :
    l * abs (Finset.sum S (fun i => a i * y i) - d * thresholdSelectedMass d S a y -
      (z - d) * thresholdSelectedMass (negativeThresholdHigh d z) S a y) <=
      Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i)) +
        (thresholdSelectedMass d S a y / negativeThresholdCurvature d z) * l ^ 2 / 4 := by
  have h := finiteWeightedNegative_joint_tilt S a y d z l hd hz ha hy hl
  have hc := negativeThreshold_constants d z hd hz
  have hCount := finiteWeightedThreshold_cutoff_antitone S a y d (negativeThresholdHigh d z) hc.2.2.le ha
  have hDiv := div_le_div_of_nonneg_right hCount hc.2.1.le
  have hMul := mul_le_mul_of_nonneg_right hDiv (sq_nonneg l)
  nlinarith only [h, hMul]

end PrimeFactorOscillations
