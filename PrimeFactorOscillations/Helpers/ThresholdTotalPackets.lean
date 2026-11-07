/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdFeasibilityExistence

/-! # Exact signed cutoff packet for the fixed-total upper face -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdTotalPacket (d v y : Real) : Real :=
  (y - v) ^ 2 - (d - v) ^ 2 * (1 - momentRoundIndicator d y)

theorem thresholdTotalPacket_selected (d v y : Real) (hy : d <= y) :
    thresholdTotalPacket d v y = (y - v) ^ 2 := by
  simp [thresholdTotalPacket, momentRoundIndicator, hy]

theorem thresholdTotalPacket_low_pos (d v y : Real) (hdv : d < v) (hy : y < d) :
    0 < thresholdTotalPacket d v y := by
  have hCut : Not (d <= y) := not_le.mpr hy
  have hIdentity : thresholdTotalPacket d v y = (y - d) * (y + d - 2 * v) := by
    simp only [thresholdTotalPacket, momentRoundIndicator, if_neg hCut, sub_zero, mul_one]
    ring
  rw [hIdentity]
  exact mul_pos_of_neg_of_neg (by linarith only [hy]) (by linarith only [hy, hdv])

theorem thresholdTotalPacket_nonneg (d v y : Real) (hdv : d < v) :
    0 <= thresholdTotalPacket d v y := by
  by_cases hCut : d <= y
  case pos => rw [thresholdTotalPacket_selected d v y hCut]; exact sq_nonneg _
  case neg => exact (thresholdTotalPacket_low_pos d v y hdv (lt_of_not_ge hCut)).le

theorem finiteWeighted_total_packet_ledger {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i)) :
    Finset.sum S (fun i => a i * thresholdTotalPacket d v (y i)) =
      (1 - 2 * v) * Finset.sum S (fun i => a i * y i) + v ^ 2 * Finset.sum S a -
        (d - v) ^ 2 * (Finset.sum S a - thresholdSelectedMass d S a y) := by
  have hExpand : Finset.sum S (fun i => a i * thresholdTotalPacket d v (y i)) =
      Finset.sum S (fun i => a i * (y i) ^ 2 - 2 * v * (a i * y i) + v ^ 2 * a i -
        (d - v) ^ 2 * (a i - a i * momentRoundIndicator d (y i))) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold thresholdTotalPacket
    ring
  rw [hExpand]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, <- Finset.mul_sum]
  rw [hMoment]
  unfold thresholdSelectedMass
  ring

theorem finiteWeighted_unselected_witness {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hLow : thresholdSelectedMass d S a y < Finset.sum S a) :
    exists i, And (Membership.mem S i) (And (0 < a i) (y i < d)) := by
  classical
  have hLowSum : Finset.sum S (fun i => a i * (1 - momentRoundIndicator d (y i))) =
      Finset.sum S a - thresholdSelectedMass d S a y := by
    simp only [thresholdSelectedMass, mul_sub, mul_one, Finset.sum_sub_distrib]
  by_contra hn
  have hZero : forall i, Membership.mem S i -> a i * (1 - momentRoundIndicator d (y i)) = 0 := by
    intro i hi
    by_cases hCut : d <= y i
    case pos => simp [momentRoundIndicator, hCut]
    case neg =>
      by_cases hp : 0 < a i
      case pos => exact False.elim (hn (Exists.intro i
        (And.intro hi (And.intro hp (lt_of_not_ge hCut)))))
      case neg =>
        have hz : a i = 0 := le_antisymm (le_of_not_gt hp) (ha i hi)
        simp [hz]
  have hSumZero := Finset.sum_eq_zero hZero
  rw [hLowSum] at hSumZero
  linarith only [hLow, hSumZero]

theorem finiteWeighted_total_packet_pos {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real) (hdv : d < v)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hLow : thresholdSelectedMass d S a y < Finset.sum S a) :
    0 < Finset.sum S (fun i => a i * thresholdTotalPacket d v (y i)) := by
  choose i hi using finiteWeighted_unselected_witness S a y d ha hLow
  exact Finset.sum_pos' (fun j hj => mul_nonneg (ha j hj) (thresholdTotalPacket_nonneg d v (y j) hdv))
    (Exists.intro i (And.intro hi.1 (mul_pos hi.2.1 (thresholdTotalPacket_low_pos d v (y i) hdv hi.2.2))))

theorem finiteWeighted_equal_moment_le_total {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i)) :
    Finset.sum S (fun i => a i * y i) <= Finset.sum S a := by
  have hPos := Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg (y i - 1)))
  have hIdentity : Finset.sum S (fun i => a i * (y i - 1) ^ 2) =
      Finset.sum S (fun i => a i * (y i) ^ 2) - 2 * Finset.sum S (fun i => a i * y i) +
        Finset.sum S a := by
    rw [Finset.mul_sum, <- Finset.sum_sub_distrib, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hIdentity, hMoment] at hPos
  linarith only [hPos]

end PrimeFactorOscillations
