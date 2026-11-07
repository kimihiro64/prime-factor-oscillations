/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdTotalFeasibility

/-! # Radial witnesses forced by the complete equal-moment row -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem finiteWeighted_threshold_le_total {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i) :
    thresholdSelectedMass d S a y <= Finset.sum S a := by
  classical
  unfold thresholdSelectedMass
  apply Finset.sum_le_sum
  intro i hi
  by_cases hCut : d <= y i
  case pos => simpa only [momentRoundIndicator, if_pos hCut, mul_one] using (_root_.le_refl (a i))
  case neg => simpa only [momentRoundIndicator, if_neg hCut, mul_zero] using ha i hi

theorem finiteWeighted_single_selected_radius {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real) (hd : And (0 < d) (d < 1)) (hv : d <= v)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hSame : forall i, Membership.mem S i -> 0 < a i -> d <= y i -> y i = v) :
    thresholdSelectedMass d S a y <= Finset.sum S (fun i => a i * y i) := by
  have hOne : 1 <= v := by
    by_contra hn
    have hvOne : v < 1 := lt_of_not_ge hn
    let r := (v + 1) / 2
    have hr : r < 1 := by dsimp [r]; linarith only [hvOne]
    choose j hj using finiteWeightedThreshold_witness S a y r hr ha hy hMoment hMass
    have hCut : d <= y j := by dsimp [r] at hj; linarith only [hv, hvOne, hj.2.2]
    have hEq := hSame j hj.1 hj.2.1 hCut
    dsimp [r] at hj
    linarith only [hvOne, hj.2.2, hEq]
  unfold thresholdSelectedMass
  apply Finset.sum_le_sum
  intro i hi
  by_cases hCut : d <= y i
  case pos =>
    by_cases hp : 0 < a i
    case pos =>
      have hEq := hSame i hi hp hCut
      have hI : momentRoundIndicator d (y i) = 1 := by simp only [momentRoundIndicator, if_pos hCut]
      rw [hI, hEq, mul_one]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne (ha i hi)
    case neg =>
      have hz : a i = 0 := le_antisymm (le_of_not_gt hp) (ha i hi)
      simp [hz]
  case neg =>
    simpa only [momentRoundIndicator, if_neg hCut, mul_zero] using mul_nonneg (ha i hi) (hy i hi)

theorem finiteWeighted_two_selected_radii {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hMK : Finset.sum S (fun i => a i * y i) < thresholdSelectedMass d S a y) :
    exists i, exists j,
      And (And (Membership.mem S i) (And (0 < a i) (d <= y i)))
        (And (And (Membership.mem S j) (And (0 < a j) (d <= y j))) (Not (y i = y j))) := by
  classical
  choose i hi using finiteWeightedThreshold_witness S a y d hd.2 ha hy hMoment hMass
  have hiCut : d <= y i := hi.2.2.le
  have hOther : exists j,
      And (And (Membership.mem S j) (And (0 < a j) (d <= y j))) (Not (y i = y j)) := by
    by_contra hn
    have hSame : forall j, Membership.mem S j -> 0 < a j -> d <= y j -> y j = y i := by
      intro j hj hp hCut
      by_contra hNe
      exact hn (Exists.intro j (And.intro (And.intro hj (And.intro hp hCut))
        (fun hEq => hNe hEq.symm)))
    have hContr := finiteWeighted_single_selected_radius S a y d (y i) hd hiCut ha hy hMoment hMass hSame
    linarith only [hContr, hMK]
  choose j hj using hOther
  exact Exists.intro i (Exists.intro j
    (And.intro (And.intro hi.1 (And.intro hi.2.1 hiCut)) hj))

theorem finiteWeighted_three_radii {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hMK : Finset.sum S (fun i => a i * y i) < thresholdSelectedMass d S a y)
    (hKN : thresholdSelectedMass d S a y < Finset.sum S a) :
    exists i, exists j, exists k,
      And (And (Membership.mem S i) (And (0 < a i) (d <= y i)))
        (And (And (Membership.mem S j) (And (0 < a j) (d <= y j)))
          (And (And (Membership.mem S k) (And (0 < a k) (y k < d))) (Not (y i = y j)))) := by
  choose i j hij using finiteWeighted_two_selected_radii S a y d hd ha hy hMoment hMass hMK
  choose k hk using finiteWeighted_unselected_witness S a y d ha hKN
  exact Exists.intro i (Exists.intro j (Exists.intro k
    (And.intro hij.1 (And.intro hij.2.1 (And.intro hk hij.2.2)))))

end PrimeFactorOscillations
