/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdBandLattice
import PrimeFactorOscillations.Helpers.ThresholdBandPackets

/-! # An arithmetic correction to the nonlinear threshold moment cost -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdIntegerCorrection (d M K : Real) : Real :=
  if K <= M then
    let z := thresholdPositiveRoot d M K
    thresholdBandPenalty (thresholdBandSlope d z) (K / thresholdBandCurvature d z)
      (thresholdBandGap d (M - K * z))
  else 0

theorem thresholdPositiveRoot_band_prediction (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hK : 0 < K) (hKM : K <= M) :
    And (M - K * thresholdPositiveRoot d M K =
      K * thresholdPositiveRoot d M K * (thresholdPositiveRoot d M K - 1) / (1 - d))
      (0 <= M - K * thresholdPositiveRoot d M K) := by
  let z := thresholdPositiveRoot d M K
  have hz := thresholdPositiveRoot_bounds d M K hd hM hK hKM
  have hr := thresholdPositiveRoot_relation d M K hd hM hK
  have hi : M - K * z = K * z * (z - 1) / (1 - d) := by
    have hD : Not (1 - d = 0) := by linarith only [hd.2]
    field_simp [hD]
    change K * z * (z - d) = (1 - d) * M at hr
    nlinarith only [hr]
  constructor
  case left => exact hi
  case right =>
    rw [hi]
    exact div_nonneg (mul_nonneg (mul_nonneg hK.le hz.1.le) (sub_nonneg.mpr hz.2))
      (by linarith only [hd.2])

theorem finiteWeightedThreshold_exact_positive_defect {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hKM : thresholdSelectedMass d S a y <= Finset.sum S (fun i => a i * y i)) :
    Finset.sum S (fun i => a i * thresholdPositivePacket d
      (thresholdPositiveRoot d (Finset.sum S (fun j => a j * y j)) (thresholdSelectedMass d S a y)) (y i)) =
    Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
      thresholdPositiveCost d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) := by
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let z := thresholdPositiveRoot d M K
  have hK := (finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass).1
  have hz := (thresholdPositiveRoot_bounds d M K hd hMass hK hKM).2
  have hr := thresholdPositiveRoot_relation d M K hd hMass hK
  have hv := thresholdPositiveValue_identity d z M K hd hz hr
  have hs := finiteWeightedThreshold_packet_sum S a y d (2 * z + thresholdPositiveMultiplier d z)
    (z ^ 2 + 2 * thresholdPositiveMultiplier d z * z) (thresholdPositiveMultiplier d z * z ^ 2) hMoment
  change Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i)) =
    Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) - thresholdPositiveCost d M K
  unfold thresholdPositiveCost
  change Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i)) =
    Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) - M * (1 - d) * (z - 1)
  change Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i)) = _ at hs
  linarith only [hs, hv]

theorem finiteWeightedThreshold_joint_tilt {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d z l : Real) (hd : And (0 < d) (d < 1)) (hz : 1 <= z)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hl : And (0 <= l) (l <= thresholdBandSlope d z)) :
    l * abs (Finset.sum S (fun i => a i * y i) - z * thresholdSelectedMass d S a y -
      d * thresholdBandMass d S a y) <=
      Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i)) +
        (thresholdSelectedMass d S a y / thresholdBandCurvature d z) * l ^ 2 / 4 := by
  have hSigned : forall s : Real, Or (s = 1) (s = -1) ->
      l * s * (Finset.sum S (fun i => a i * y i) - z * thresholdSelectedMass d S a y -
        d * thresholdBandMass d S a y) <=
      Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i)) +
        (thresholdSelectedMass d S a y / thresholdBandCurvature d z) * l ^ 2 / 4 := by
    intro s hs
    have hSum := Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi)
      (thresholdBand_tilted_packet d z (y i) l s hd hz (hy i hi) hl hs))
    have hIdentity : Finset.sum S (fun i => a i * (thresholdPositivePacket d z (y i) +
        l ^ 2 / (4 * thresholdBandCurvature d z) * momentRoundIndicator d (y i) -
        l * s * (y i - z * momentRoundIndicator d (y i) - d * thresholdBandIndicator d (y i)))) =
      Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i)) +
        (thresholdSelectedMass d S a y / thresholdBandCurvature d z) * l ^ 2 / 4 -
        l * s * (Finset.sum S (fun i => a i * y i) - z * thresholdSelectedMass d S a y -
          d * thresholdBandMass d S a y) := by
      calc
        _ = Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i) +
            (l ^ 2 / (4 * thresholdBandCurvature d z)) * (a i * momentRoundIndicator d (y i)) -
            (l * s) * (a i * y i) + (l * s * z) * (a i * momentRoundIndicator d (y i)) +
            (l * s * d) * (a i * thresholdBandIndicator d (y i))) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          unfold thresholdSelectedMass thresholdBandMass
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]
          ring
    rw [hIdentity] at hSum
    linarith only [hSum]
  by_cases h : 0 <= Finset.sum S (fun i => a i * y i) - z * thresholdSelectedMass d S a y -
      d * thresholdBandMass d S a y
  case pos =>
    rw [abs_of_nonneg h]
    simpa only [mul_one] using hSigned 1 (Or.inl rfl)
  case neg =>
    rw [abs_of_nonpos (le_of_lt (lt_of_not_ge h))]
    have hs := hSigned (-1) (Or.inr rfl)
    nlinarith only [hs]

theorem finiteWeightedThreshold_integer_cost {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hBand : exists m : Nat, thresholdBandMass d S a y = 2 * (m : Real)) :
    thresholdNonlinearCost d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) +
      thresholdIntegerCorrection d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) <=
        Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  by_cases hKM : K <= M
  case pos =>
    let z := thresholdPositiveRoot d M K
    let A := thresholdBandSlope d z
    let B := K / thresholdBandCurvature d z
    let eta := thresholdBandGap d (M - K * z)
    have hK := (finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass).1
    have hz := (thresholdPositiveRoot_bounds d M K hd hMass hK hKM).2
    have hConstants := thresholdBand_constants_pos d z hd hz
    have hB : 0 < B := div_pos hK hConstants.2
    have hp := (thresholdPositiveRoot_band_prediction d M K hd hMass hK hKM).2
    have he := thresholdBandGap_nonneg d (M - K * z) hd.1 hp
    choose m hm using hBand
    have hDist := thresholdBandGap_le_distance d (M - K * z) hd.1 hp m
    have hDefect := finiteWeightedThreshold_exact_positive_defect S a y d hd ha hy hMoment hMass hKM
    have hTilt : forall l : Real, 0 <= l -> l <= A -> l * eta - B * l ^ 2 / 4 <=
        Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) - thresholdPositiveCost d M K := by
      intro l hl hu
      have ht := finiteWeightedThreshold_joint_tilt S a y d z l hd hz ha hy (And.intro hl hu)
      rw [hDefect] at ht
      have hDist' : eta <= abs (M - z * K - d * thresholdBandMass d S a y) := by
        rw [hm]
        convert hDist using 1 <;> congr 1 <;> ring
      have hm' := mul_le_mul_of_nonneg_left hDist' hl
      nlinarith only [ht, hm']
    have hPenalty := thresholdBandPenalty_le A B eta _ hConstants.1 hB he hTilt
    change thresholdNonlinearCost d M K + thresholdIntegerCorrection d M K <= _
    simp only [thresholdNonlinearCost, thresholdIntegerCorrection, if_pos hKM]
    exact (by linarith only [hPenalty])
  case neg =>
    have hCost := finiteWeightedThreshold_nonlinear_cost S a y d hd ha hy hMoment hMass
    change thresholdNonlinearCost d M K + thresholdIntegerCorrection d M K <= _
    simp only [thresholdIntegerCorrection, if_neg hKM, add_zero]
    exact hCost

theorem thresholdIntegerCorrection_nonneg (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hK : 0 < K) :
    0 <= thresholdIntegerCorrection d M K := by
  unfold thresholdIntegerCorrection
  split_ifs with h
  case pos =>
    have hz := (thresholdPositiveRoot_bounds d M K hd hM hK h).2
    have hc := thresholdBand_constants_pos d _ hd hz
    have hp := (thresholdPositiveRoot_band_prediction d M K hd hM hK h).2
    exact thresholdBandPenalty_nonneg _ _ _ hc.1 (div_pos hK hc.2)
      (thresholdBandGap_nonneg d _ hd.1 hp)
  case neg => exact le_refl 0

end PrimeFactorOscillations
