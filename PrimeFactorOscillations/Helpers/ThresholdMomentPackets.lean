/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DirectionalParityStability

/-! # Cubic threshold packets with both exact moment constraints -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdSelectedMass {Iota : Type*} (d : Real) (S : Finset Iota)
    (a y : Iota -> Real) : Real :=
  Finset.sum S (fun i => a i * momentRoundIndicator d (y i))

def thresholdPositiveMultiplier (d z : Real) : Real := -(z - d) ^ 2 / (2 * z - d)

def thresholdPositivePacket (d z y : Real) : Real :=
  y ^ 3 - (2 * z + thresholdPositiveMultiplier d z) * y ^ 2 +
    (z ^ 2 + 2 * thresholdPositiveMultiplier d z * z) * y -
      thresholdPositiveMultiplier d z * z ^ 2 * momentRoundIndicator d y

def thresholdNegativePacket (d z y : Real) : Real :=
  y ^ 3 - (2 * z + d) * y ^ 2 + (z ^ 2 + 2 * d * z) * y -
    d * z ^ 2 * momentRoundIndicator d y

theorem thresholdIndicator_nonneg (d y : Real) : 0 <= momentRoundIndicator d y := by
  classical
  unfold momentRoundIndicator
  split_ifs <;> norm_num

theorem thresholdIndicator_defect_nonneg (d y : Real) (hy : 0 <= y) :
    0 <= y - d * momentRoundIndicator d y := by
  classical
  by_cases hh : d <= y
  case pos => simpa [momentRoundIndicator, hh] using sub_nonneg.mpr hh
  case neg => simpa [momentRoundIndicator, hh] using hy

theorem finiteWeightedThreshold_witness {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : d < 1)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    exists i, And (Membership.mem S i) (And (0 < a i) (d < y i)) := by
  by_contra hn
  have hEach : forall i, Membership.mem S i -> a i * (y i) ^ 2 <= d * (a i * y i) := by
    intro i hi
    by_cases hp : 0 < a i
    case pos =>
      have hY : y i <= d := le_of_not_gt (fun hgt =>
        hn (Exists.intro i (And.intro hi (And.intro hp hgt))))
      have hm := mul_nonneg (mul_nonneg (ha i hi) (hy i hi)) (sub_nonneg.mpr hY)
      nlinarith only [hm]
    case neg =>
      have hz : a i = 0 := le_antisymm (le_of_not_gt hp) (ha i hi)
      simp [hz]
  have hSum := Finset.sum_le_sum hEach
  rw [hMoment, <- Finset.mul_sum] at hSum
  have hGap := mul_pos (sub_pos.mpr hd) hMass
  nlinarith only [hSum, hGap]

theorem finiteWeightedThreshold_domain {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : d < 1)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    And (0 < thresholdSelectedMass d S a y)
      (d * thresholdSelectedMass d S a y < Finset.sum S (fun i => a i * y i)) := by
  classical
  choose i hi using finiteWeightedThreshold_witness S a y d hd ha hy hMoment hMass
  have hCut : d <= y i := hi.2.2.le
  have hTerm : 0 < a i * momentRoundIndicator d (y i) := by
    simpa [momentRoundIndicator, hCut] using hi.2.1
  have hCount : 0 < thresholdSelectedMass d S a y :=
    Finset.sum_pos' (fun j hj => mul_nonneg (ha j hj) (thresholdIndicator_nonneg d (y j)))
      (Exists.intro i (And.intro hi.1 hTerm))
  have hDefects : forall j, Membership.mem S j -> 0 <= a j *
      (y j - d * momentRoundIndicator d (y j)) :=
    fun j hj => mul_nonneg (ha j hj) (thresholdIndicator_defect_nonneg d (y j) (hy j hj))
  have hDefect : 0 < a i * (y i - d * momentRoundIndicator d (y i)) := by
    have hh := mul_pos hi.2.1 (sub_pos.mpr hi.2.2)
    simpa [momentRoundIndicator, hCut] using hh
  have hSum := Finset.sum_pos' hDefects (Exists.intro i (And.intro hi.1 hDefect))
  have hIdentity : Finset.sum S (fun j => a j * (y j - d * momentRoundIndicator d (y j))) =
      Finset.sum S (fun j => a j * y j) - d * thresholdSelectedMass d S a y := by
    unfold thresholdSelectedMass
    rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hIdentity] at hSum
  exact And.intro hCount (by linarith only [hSum])

theorem thresholdPositiveMultiplier_bounds (d z : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) :
    And (thresholdPositiveMultiplier d z < 0)
      (d < 2 * z + thresholdPositiveMultiplier d z - d) := by
  have hDen : 0 < 2 * z - d := by linarith only [hd.2, hz]
  have hZD : 0 < z - d := by linarith only [hd.2, hz]
  have hB : thresholdPositiveMultiplier d z < 0 := by
    unfold thresholdPositiveMultiplier
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hZD)) hDen
  have hIdentity : (2 * z + thresholdPositiveMultiplier d z - d) - d =
      (z - d) * (3 * z - d) / (2 * z - d) := by
    unfold thresholdPositiveMultiplier
    field_simp [hDen.ne']
    ring
  have hPos : 0 < (z - d) * (3 * z - d) / (2 * z - d) :=
    div_pos (mul_pos hZD (by linarith only [hz, hd.2])) hDen
  exact And.intro hB (by linarith only [hIdentity, hPos])

theorem thresholdPositivePacket_selected (d z y : Real) (hy : d <= y) :
    thresholdPositivePacket d z y = (y - z) ^ 2 * (y - thresholdPositiveMultiplier d z) := by
  classical
  unfold thresholdPositivePacket momentRoundIndicator
  rw [if_pos hy]
  ring

theorem thresholdPositivePacket_unselected (d z y : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) (hy : y < d) :
    thresholdPositivePacket d z y = y * (y - d) *
      (y - (2 * z + thresholdPositiveMultiplier d z - d)) := by
  classical
  have hDen : 0 < 2 * z - d := by linarith only [hd.2, hz]
  unfold thresholdPositivePacket momentRoundIndicator
  rw [if_neg (not_le.mpr hy)]
  unfold thresholdPositiveMultiplier
  field_simp [hDen.ne']
  ring

theorem thresholdPositivePacket_nonneg (d z y : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) (hy : 0 <= y) :
    0 <= thresholdPositivePacket d z y := by
  have hb := thresholdPositiveMultiplier_bounds d z hd hz
  by_cases hCut : d <= y
  case pos =>
    rw [thresholdPositivePacket_selected d z y hCut]
    exact mul_nonneg (sq_nonneg _) (by linarith only [hy, hb.1])
  case neg =>
    have hLow : y < d := lt_of_not_ge hCut
    rw [thresholdPositivePacket_unselected d z y hd hz hLow]
    have hm := mul_nonneg hy (mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hLow.le) (show y - (2 * z + thresholdPositiveMultiplier d z - d) <= 0 by
        linarith only [hLow, hb.2]))
    simpa only [mul_assoc] using hm

theorem thresholdNegativePacket_selected (d z y : Real) (hy : d <= y) :
    thresholdNegativePacket d z y = (y - d) * (y - z) ^ 2 := by
  classical
  unfold thresholdNegativePacket momentRoundIndicator
  rw [if_pos hy]
  ring

theorem thresholdNegativePacket_unselected (d z y : Real) (hy : y < d) :
    thresholdNegativePacket d z y = y * ((y - d) * (y - 2 * z) + z ^ 2) := by
  classical
  unfold thresholdNegativePacket momentRoundIndicator
  rw [if_neg (not_le.mpr hy)]
  ring

theorem thresholdNegativePacket_nonneg (d z y : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) (hy : 0 <= y) :
    0 <= thresholdNegativePacket d z y := by
  by_cases hCut : d <= y
  case pos =>
    rw [thresholdNegativePacket_selected d z y hCut]
    exact mul_nonneg (sub_nonneg.mpr hCut) (sq_nonneg _)
  case neg =>
    have hLow : y < d := lt_of_not_ge hCut
    rw [thresholdNegativePacket_unselected d z y hLow]
    have hm := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hLow.le)
      (show y - 2 * z <= 0 by linarith only [hLow, hd.2, hz])
    exact mul_nonneg hy (add_nonneg hm (sq_nonneg z))

theorem finiteWeightedThreshold_packet_sum {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d p q r : Real)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i)) :
    Finset.sum S (fun i => a i * ((y i) ^ 3 - p * (y i) ^ 2 + q * y i -
      r * momentRoundIndicator d (y i))) =
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
        (p - q - 1) * Finset.sum S (fun i => a i * y i) - r * thresholdSelectedMass d S a y := by
  calc
    _ = Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2 -
        (p - q - 1) * (a i * y i) - r * (a i * momentRoundIndicator d (y i)) +
        (2 - p) * (a i * (y i) ^ 2 - a i * y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      unfold thresholdSelectedMass
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum, hMoment]
      ring

theorem finiteWeightedThreshold_positive_packet {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d z : Real) (hd : And (0 < d) (d < 1)) (hz : 1 <= z)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i)) :
    (2 * z + thresholdPositiveMultiplier d z - (z ^ 2 + 2 * thresholdPositiveMultiplier d z * z) - 1) *
      Finset.sum S (fun i => a i * y i) +
        (thresholdPositiveMultiplier d z * z ^ 2) * thresholdSelectedMass d S a y <=
          Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  have hSum := Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi)
    (thresholdPositivePacket_nonneg d z (y i) hd hz (hy i hi)))
  change 0 <= Finset.sum S (fun i => a i * ((y i) ^ 3 -
    (2 * z + thresholdPositiveMultiplier d z) * (y i) ^ 2 +
    (z ^ 2 + 2 * thresholdPositiveMultiplier d z * z) * y i -
    (thresholdPositiveMultiplier d z * z ^ 2) * momentRoundIndicator d (y i))) at hSum
  rw [finiteWeightedThreshold_packet_sum S a y d _ _ _ hMoment] at hSum
  linarith only [hSum]

theorem finiteWeightedThreshold_negative_packet {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d z : Real) (hd : And (0 < d) (d < 1)) (hz : 1 <= z)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i)) :
    (2 * z + d - (z ^ 2 + 2 * d * z) - 1) * Finset.sum S (fun i => a i * y i) +
      d * z ^ 2 * thresholdSelectedMass d S a y <=
        Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  have hSum := Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi)
    (thresholdNegativePacket_nonneg d z (y i) hd hz (hy i hi)))
  change 0 <= Finset.sum S (fun i => a i * ((y i) ^ 3 -
    (2 * z + d) * (y i) ^ 2 + (z ^ 2 + 2 * d * z) * y i -
    (d * z ^ 2) * momentRoundIndicator d (y i))) at hSum
  rw [finiteWeightedThreshold_packet_sum S a y d _ _ _ hMoment] at hSum
  linarith only [hSum]

end PrimeFactorOscillations
