/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NegativeThresholdPackets
import PrimeFactorOscillations.Helpers.ThresholdEvenSharpness

/-! # The negative arithmetic gap and the complete two-sided energy cost -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdNegativeIntegerCorrection (d M K : Real) : Real :=
  if M < K then
    let z := thresholdNegativeRoot d M K
    thresholdBandPenalty (negativeThresholdSlope d z) (K / negativeThresholdCurvature d z)
      (thresholdBandGap (z - d) (M - d * K))
  else 0

def thresholdTwoSidedIntegerCorrection (d M K : Real) : Real :=
  thresholdIntegerCorrection d M K + thresholdNegativeIntegerCorrection d M K

theorem finiteWeightedThreshold_exact_negative_defect {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hDomain : d * thresholdSelectedMass d S a y < Finset.sum S (fun i => a i * y i)) :
    Finset.sum S (fun i => a i * thresholdNegativePacket d
      (thresholdNegativeRoot d (Finset.sum S (fun j => a j * y j)) (thresholdSelectedMass d S a y)) (y i)) =
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
        thresholdNegativeCost d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) := by
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let z := thresholdNegativeRoot d M K
  have hv := thresholdNegativeValue_identity d z M K (thresholdNegativeRoot_relation d M K hDomain)
  have hs := finiteWeightedThreshold_packet_sum S a y d (2 * z + d)
    (z ^ 2 + 2 * d * z) (d * z ^ 2) hMoment
  change Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i)) = _ at hs
  change Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i)) =
    Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) - thresholdNegativeCost d M K
  rw [thresholdNegativeCost_root]
  linarith only [hs, hv]

theorem finiteWeightedNegative_integer_cost {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hMK : Finset.sum S (fun i => a i * y i) < thresholdSelectedMass d S a y)
    (hHigh : exists m : Nat, thresholdSelectedMass (negativeThresholdHigh d
      (thresholdNegativeRoot d (Finset.sum S (fun j => a j * y j)) (thresholdSelectedMass d S a y))) S a y = 2 * (m : Real)) :
    thresholdNonlinearCost d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) +
      thresholdNegativeIntegerCorrection d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) <=
        Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let z := thresholdNegativeRoot d M K
  let A := negativeThresholdSlope d z
  let B := K / negativeThresholdCurvature d z
  let eta := thresholdBandGap (z - d) (M - d * K)
  have hDomain := finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass
  have hz := thresholdNegativeRoot_ge_one d M K hd.1 hDomain.2 hMK.le
  have hc := negativeThreshold_constants d z hd hz
  have hg : 0 < z - d := by linarith only [hz, hd.2]
  have he := thresholdBandGap_nonneg (z - d) (M - d * K) hg (sub_nonneg.mpr hDomain.2.le)
  have hB : 0 < B := div_pos hDomain.1 hc.2.1
  choose m hm using hHigh
  have hDist := thresholdBandGap_le_distance (z - d) (M - d * K) hg (sub_nonneg.mpr hDomain.2.le) m
  have hDefect := finiteWeightedThreshold_exact_negative_defect S a y d hMoment hDomain.2
  have hTilt : forall l : Real, 0 <= l -> l <= A -> l * eta - B * l ^ 2 / 4 <=
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) - thresholdNegativeCost d M K := by
    intro l hl hu
    have ht := finiteWeightedNegative_joint_budget S a y d z l hd hz ha hy (And.intro hl hu)
    rw [hDefect] at ht
    have hDist' : eta <= abs (M - d * K - (z - d) * thresholdSelectedMass (negativeThresholdHigh d z) S a y) := by
      rw [hm]
      convert hDist using 1 <;> congr 1 <;> ring
    have hm' := mul_le_mul_of_nonneg_left hDist' hl
    nlinarith only [ht, hm']
  have hPenalty := thresholdBandPenalty_le A B eta _ hc.1 hB he hTilt
  have hSide : M < K := hMK
  change thresholdNonlinearCost d M K + thresholdNegativeIntegerCorrection d M K <= _
  simp only [thresholdNonlinearCost, thresholdNegativeIntegerCorrection, if_neg (not_le.mpr hSide), if_pos hSide]
  change thresholdNegativeCost d M K + thresholdBandPenalty A B eta <= _
  linarith only [hPenalty]

theorem thresholdNegativeIntegerCorrection_nonneg (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K) (hDomain : d * K < M) :
    0 <= thresholdNegativeIntegerCorrection d M K := by
  unfold thresholdNegativeIntegerCorrection
  split_ifs with h
  case pos =>
    have hz := thresholdNegativeRoot_ge_one d M K hd.1 hDomain h.le
    have hc := negativeThreshold_constants d _ hd hz
    have hg : 0 < thresholdNegativeRoot d M K - d := by linarith only [hz, hd.2]
    exact thresholdBandPenalty_nonneg _ _ _ hc.1 (div_pos hK hc.2.1)
      (thresholdBandGap_nonneg _ _ hg (sub_nonneg.mpr hDomain.le))
  case neg => exact le_refl 0

theorem thresholdNegativeIntegerCorrection_pos (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K) (hDomain : d * K < M) (hMK : M < K)
    (hGap : 0 < thresholdBandGap (thresholdNegativeRoot d M K - d) (M - d * K)) :
    0 < thresholdNegativeIntegerCorrection d M K := by
  have hz := thresholdNegativeRoot_ge_one d M K hd.1 hDomain hMK.le
  have hc := negativeThreshold_constants d _ hd hz
  unfold thresholdNegativeIntegerCorrection
  rw [if_pos hMK]
  exact thresholdBandPenalty_pos _ _ _ hc.1 (div_pos hK hc.2.1) hGap

theorem thresholdSelectedMass_even_weights {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d : Real) :
    exists m : Nat, thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y = 2 * (m : Real) := by
  classical
  let q := fun i => if d <= y i then a i else 0
  apply Exists.intro (Finset.sum S q)
  unfold thresholdSelectedMass
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : d <= y i
  case pos => simp [momentRoundIndicator, q, h]
  case neg => simp [momentRoundIndicator, q, h]

theorem thresholdEven_negative_lower {n : Nat} (d M K : Real) (a : Fin n -> Nat) (y : Fin n -> Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hMK : M < K)
    (hAd : thresholdEvenAdmissible d M K a y) :
    thresholdNonlinearCost d M K + thresholdNegativeIntegerCorrection d M K <= thresholdEvenEnergy a y := by
  have hMoment : Finset.sum Finset.univ (fun i => 2 * (a i : Real) * (y i) ^ 2) =
      Finset.sum Finset.univ (fun i => 2 * (a i : Real) * y i) := hAd.2.2.1.trans hAd.2.1.symm
  have hMass : 0 < Finset.sum Finset.univ (fun i => 2 * (a i : Real) * y i) := by
    rw [hAd.2.1]
    exact hM
  have hSide : Finset.sum Finset.univ (fun i => 2 * (a i : Real) * y i) <
      thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y := by
    rw [hAd.2.1, hAd.2.2.2]
    exact hMK
  have hBound := finiteWeightedNegative_integer_cost Finset.univ (fun i => 2 * (a i : Real)) y d hd
    (fun i _ => mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (fun i _ => hAd.1 i)
    hMoment hMass hSide (thresholdSelectedMass_even_weights Finset.univ a y _)
  rw [hAd.2.1, hAd.2.2.2] at hBound
  exact hBound

theorem thresholdEven_two_sided_lower {n : Nat} (d M K : Real) (a : Fin n -> Nat) (y : Fin n -> Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hAd : thresholdEvenAdmissible d M K a y) :
    thresholdNonlinearCost d M K + thresholdTwoSidedIntegerCorrection d M K <= thresholdEvenEnergy a y := by
  unfold thresholdTwoSidedIntegerCorrection
  by_cases h : K <= M
  case pos =>
    simp only [thresholdNegativeIntegerCorrection, if_neg (not_lt.mpr h), add_zero]
    exact thresholdEven_integer_lower d M K a y hd hM hAd
  case neg =>
    simp only [thresholdIntegerCorrection, if_neg h, zero_add]
    exact thresholdEven_negative_lower d M K a y hd hM (lt_of_not_ge h) hAd

end PrimeFactorOscillations
