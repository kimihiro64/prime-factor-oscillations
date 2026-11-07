/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdMomentPackets

/-! # Explicit nonlinear lower costs for both threshold discrepancies -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdPositiveRoot (d M K : Real) : Real :=
  (d + Real.sqrt (d ^ 2 + 4 * (1 - d) * M / K)) / 2

def thresholdNegativeRoot (d M K : Real) : Real := M * (1 - d) / (M - d * K)

def thresholdPositiveCost (d M K : Real) : Real :=
  M * (1 - d) * (thresholdPositiveRoot d M K - 1)

def thresholdNegativeCost (d M K : Real) : Real :=
  d * M * (1 - d) * (K - M) / (M - d * K)

def thresholdNonlinearCost (d M K : Real) : Real :=
  if K <= M then thresholdPositiveCost d M K else thresholdNegativeCost d M K

theorem thresholdPositiveRoot_equation (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hK : 0 < K) :
    thresholdPositiveRoot d M K * (thresholdPositiveRoot d M K - d) = (1 - d) * M / K := by
  have hDisc : 0 <= d ^ 2 + 4 * (1 - d) * M / K := by
    have hOne : 0 < 1 - d := sub_pos.mpr hd.2
    positivity
  have hSquare := Real.sq_sqrt hDisc
  unfold thresholdPositiveRoot
  calc
    _ = (Real.sqrt (d ^ 2 + 4 * (1 - d) * M / K)) ^ 2 / 4 - d ^ 2 / 4 := by ring
    _ = (d ^ 2 + 4 * (1 - d) * M / K) / 4 - d ^ 2 / 4 := by rw [hSquare]
    _ = _ := by ring

theorem thresholdPositiveRoot_relation (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hK : 0 < K) :
    K * thresholdPositiveRoot d M K * (thresholdPositiveRoot d M K - d) = (1 - d) * M := by
  calc
    _ = K * (thresholdPositiveRoot d M K * (thresholdPositiveRoot d M K - d)) := by ring
    _ = K * ((1 - d) * M / K) := by rw [thresholdPositiveRoot_equation d M K hd hM hK]
    _ = _ := by field_simp [hK.ne']

theorem thresholdPositiveRoot_bounds (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hK : 0 < K) (hKM : K <= M) :
    And (0 < thresholdPositiveRoot d M K) (1 <= thresholdPositiveRoot d M K) := by
  have hzPos : 0 < thresholdPositiveRoot d M K := by
    unfold thresholdPositiveRoot
    have hs := Real.sqrt_nonneg (d ^ 2 + 4 * (1 - d) * M / K)
    linarith only [hd.1, hs]
  have hRoot := thresholdPositiveRoot_relation d M K hd hM hK
  have hCompare := _root_.mul_le_mul_of_nonneg_left hKM (sub_nonneg.mpr hd.2.le)
  have hzOne : 1 <= thresholdPositiveRoot d M K := by
    by_contra hn
    have hz : thresholdPositiveRoot d M K < 1 := lt_of_not_ge hn
    have hProduct := mul_neg_of_neg_of_pos (sub_neg.mpr hz)
      (show 0 < thresholdPositiveRoot d M K + 1 - d by linarith only [hzPos, hd.2])
    have hScaled := mul_neg_of_pos_of_neg hK hProduct
    nlinarith only [hRoot, hCompare, hScaled]
  exact And.intro hzPos hzOne

theorem thresholdPositiveRoot_gt_one (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hK : 0 < K) (hKM : K < M) :
    1 < thresholdPositiveRoot d M K := by
  have hz := (thresholdPositiveRoot_bounds d M K hd hM hK hKM.le).2
  have hRoot := thresholdPositiveRoot_relation d M K hd hM hK
  by_contra hn
  have hEq : thresholdPositiveRoot d M K = 1 := le_antisymm (le_of_not_gt hn) hz
  rw [hEq] at hRoot
  have hGap := mul_pos (sub_pos.mpr hd.2) (sub_pos.mpr hKM)
  nlinarith only [hRoot, hGap]

theorem thresholdNegativeRoot_relation (d M K : Real) (hDomain : d * K < M) :
    d * thresholdNegativeRoot d M K * K = M * (thresholdNegativeRoot d M K - 1 + d) := by
  have hDen : 0 < M - d * K := sub_pos.mpr hDomain
  unfold thresholdNegativeRoot
  field_simp [hDen.ne']
  ring

theorem thresholdNegativeRoot_ge_one (d M K : Real)
    (hd : 0 < d) (hDomain : d * K < M) (hMK : M <= K) :
    1 <= thresholdNegativeRoot d M K := by
  have hDen : 0 < M - d * K := sub_pos.mpr hDomain
  have hIdentity : (M - d * K) * (thresholdNegativeRoot d M K - 1) = d * (K - M) := by
    unfold thresholdNegativeRoot
    field_simp [hDen.ne']
    ring
  have hNonneg := mul_nonneg hd.le (sub_nonneg.mpr hMK)
  by_contra hn
  have hNeg := mul_neg_of_pos_of_neg hDen (sub_neg.mpr (lt_of_not_ge hn))
  nlinarith only [hIdentity, hNonneg, hNeg]

theorem thresholdNegativeCost_root (d M K : Real) :
    thresholdNegativeCost d M K = d * thresholdNegativeRoot d M K * (K - M) := by
  unfold thresholdNegativeCost thresholdNegativeRoot
  ring

theorem thresholdPositiveValue_identity (d z M K : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z)
    (hRelation : K * z * (z - d) = (1 - d) * M) :
    (2 * z + thresholdPositiveMultiplier d z - (z ^ 2 + 2 * thresholdPositiveMultiplier d z * z) - 1) * M +
      (thresholdPositiveMultiplier d z * z ^ 2) * K = M * (1 - d) * (z - 1) := by
  have hDen : 0 < 2 * z - d := by linarith only [hd.2, hz]
  have hIdentity :
      ((2 * z + thresholdPositiveMultiplier d z - (z ^ 2 + 2 * thresholdPositiveMultiplier d z * z) - 1) * M +
        (thresholdPositiveMultiplier d z * z ^ 2) * K - M * (1 - d) * (z - 1)) * (2 * z - d) =
      z * (z - d) * ((1 - d) * M - K * z * (z - d)) := by
    unfold thresholdPositiveMultiplier
    field_simp [hDen.ne'] <;> ring
  rw [<- hRelation, sub_self, mul_zero] at hIdentity
  have hZero := (mul_eq_zero.mp hIdentity).resolve_right hDen.ne'
  linarith only [hZero]

theorem thresholdNegativeValue_identity (d z M K : Real)
    (hRelation : d * z * K = M * (z - 1 + d)) :
    (2 * z + d - (z ^ 2 + 2 * d * z) - 1) * M + d * z ^ 2 * K = d * z * (K - M) := by
  have hIdentity : (2 * z + d - (z ^ 2 + 2 * d * z) - 1) * M + d * z ^ 2 * K -
      d * z * (K - M) = (z - 1) * (d * z * K - M * (z - 1 + d)) := by ring
  rw [hRelation, sub_self, mul_zero] at hIdentity
  linarith only [hIdentity]

theorem finiteWeightedThreshold_positive_cost {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hKM : thresholdSelectedMass d S a y <= Finset.sum S (fun i => a i * y i)) :
    thresholdPositiveCost d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) <=
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let z := thresholdPositiveRoot d M K
  have hDomain := finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass
  have hz : 1 <= z := (thresholdPositiveRoot_bounds d M K hd hMass hDomain.1 hKM).2
  have hPacket := finiteWeightedThreshold_positive_packet S a y d z hd hz ha hy hMoment
  change (2 * z + thresholdPositiveMultiplier d z - (z ^ 2 + 2 * thresholdPositiveMultiplier d z * z) - 1) * M +
    (thresholdPositiveMultiplier d z * z ^ 2) * K <= _ at hPacket
  rw [thresholdPositiveValue_identity d z M K hd hz
    (thresholdPositiveRoot_relation d M K hd hMass hDomain.1)] at hPacket
  exact hPacket

theorem finiteWeightedThreshold_negative_cost {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hMK : Finset.sum S (fun i => a i * y i) <= thresholdSelectedMass d S a y) :
    thresholdNegativeCost d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) <=
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let z := thresholdNegativeRoot d M K
  have hDomain := finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass
  have hz : 1 <= z := thresholdNegativeRoot_ge_one d M K hd.1 hDomain.2 hMK
  have hPacket := finiteWeightedThreshold_negative_packet S a y d z hd hz ha hy hMoment
  change (2 * z + d - (z ^ 2 + 2 * d * z) - 1) * M + d * z ^ 2 * K <= _ at hPacket
  rw [thresholdNegativeValue_identity d z M K (thresholdNegativeRoot_relation d M K hDomain.2)] at hPacket
  rw [thresholdNegativeCost_root]
  exact hPacket

theorem finiteWeightedThreshold_nonlinear_cost {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    thresholdNonlinearCost d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) <=
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  unfold thresholdNonlinearCost
  by_cases hSide : thresholdSelectedMass d S a y <= Finset.sum S (fun i => a i * y i)
  case pos =>
    rw [if_pos hSide]
    exact finiteWeightedThreshold_positive_cost S a y d hd ha hy hMoment hMass hSide
  case neg =>
    rw [if_neg hSide]
    exact finiteWeightedThreshold_negative_cost S a y d hd ha hy hMoment hMass (lt_of_not_ge hSide).le

end PrimeFactorOscillations
