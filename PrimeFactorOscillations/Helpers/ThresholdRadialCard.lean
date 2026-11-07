/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Card
import PrimeFactorOscillations.Helpers.ThresholdRadialWitness

/-! # Distinct positive-weight radii and exact small-support rigidity -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdRadialSupport {Iota : Type*} (S : Finset Iota) (a y : Iota -> Real) : Finset Real := by
  classical
  exact (S.filter (fun i => 0 < a i)).image y

theorem thresholdRadialSupport_mem {Iota : Type*} (S : Finset Iota) (a y : Iota -> Real) (z : Real) :
    Membership.mem (thresholdRadialSupport S a y) z <->
      exists i, And (Membership.mem S i) (And (0 < a i) (y i = z)) := by
  classical
  unfold thresholdRadialSupport
  constructor
  case mp =>
    intro h
    choose i hi using Finset.mem_image.mp h
    have hm := Finset.mem_filter.mp hi.1
    exact Exists.intro i (And.intro hm.1 (And.intro hm.2 hi.2))
  case mpr =>
    intro h
    choose i hi using h
    exact Finset.mem_image.mpr (Exists.intro i
      (And.intro (Finset.mem_filter.mpr (And.intro hi.1 hi.2.1)) hi.2.2))

theorem thresholdRadialSupport_card_le {Iota : Type*} (S : Finset Iota) (a y : Iota -> Real) :
    (thresholdRadialSupport S a y).card <= S.card := by
  classical
  unfold thresholdRadialSupport
  exact le_trans Finset.card_image_le (Finset.card_filter_le S (fun i => 0 < a i))

theorem thresholdRadialSupport_card_le_fin {r : Nat} (a y : Fin r -> Real) :
    (thresholdRadialSupport Finset.univ a y).card <= r := by
  have h := thresholdRadialSupport_card_le Finset.univ a y
  simpa only [Finset.card_univ, Fintype.card_fin] using h

theorem finiteWeighted_radius_card_pos {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    1 <= (thresholdRadialSupport S a y).card := by
  choose i hi using finiteWeightedThreshold_witness S a y 0 (by norm_num) ha hy hMoment hMass
  have hm := (thresholdRadialSupport_mem S a y (y i)).mpr
    (Exists.intro i (And.intro hi.1 (And.intro hi.2.1 rfl)))
  have hNonempty : (thresholdRadialSupport S a y).Nonempty := Exists.intro (y i) hm
  have hPos := Finset.card_pos.mpr hNonempty
  omega

theorem finiteWeighted_three_radius_card {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hMK : Finset.sum S (fun i => a i * y i) < thresholdSelectedMass d S a y)
    (hKN : thresholdSelectedMass d S a y < Finset.sum S a) :
    3 <= (thresholdRadialSupport S a y).card := by
  classical
  choose i j k h using finiteWeighted_three_radii S a y d hd ha hy hMoment hMass hMK hKN
  have hi := h.1
  have hj := h.2.1
  have hk := h.2.2.1
  have hIJ := h.2.2.2
  have hIK : Not (y i = y k) := by intro heq; linarith only [hi.2.2, hk.2.2, heq]
  have hJK : Not (y j = y k) := by intro heq; linarith only [hj.2.2, hk.2.2, heq]
  have hMi := (thresholdRadialSupport_mem S a y (y i)).mpr
    (Exists.intro i (And.intro hi.1 (And.intro hi.2.1 rfl)))
  have hMj := (thresholdRadialSupport_mem S a y (y j)).mpr
    (Exists.intro j (And.intro hj.1 (And.intro hj.2.1 rfl)))
  have hMk := (thresholdRadialSupport_mem S a y (y k)).mpr
    (Exists.intro k (And.intro hk.1 (And.intro hk.2.1 rfl)))
  have hSubset : forall z, Membership.mem ({y i, y j, y k} : Finset Real) z ->
      Membership.mem (thresholdRadialSupport S a y) z := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzi | hzj | hzk
    case inl => simpa only [hzi] using hMi
    case inr.inl => simpa only [hzj] using hMj
    case inr.inr => simpa only [hzk] using hMk
  have hCard : ({y i, y j, y k} : Finset Real).card = 3 := by simp [hIJ, hIK, hJK]
  have hLe := Finset.card_le_card hSubset
  rw [hCard] at hLe
  exact hLe

theorem finiteWeighted_constant_radius_rigid {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real) (hd : d < 1)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hSame : forall i, Membership.mem S i -> 0 < a i -> y i = v) :
    And (Finset.sum S (fun i => a i * y i) = Finset.sum S a)
      (thresholdSelectedMass d S a y = Finset.sum S a) := by
  have hSecond : Finset.sum S (fun i => a i * (y i) ^ 2) =
      v * Finset.sum S (fun i => a i * y i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : 0 < a i
    case pos => rw [hSame i hi hp]; ring
    case neg =>
      have hz : a i = 0 := le_antisymm (le_of_not_gt hp) (ha i hi)
      simp [hz]
  have hFactor : (v - 1) * Finset.sum S (fun i => a i * y i) = 0 := by
    nlinarith only [hSecond, hMoment]
  have hV : v = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hFactor).resolve_right hMass.ne')
  constructor
  case left =>
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : 0 < a i
    case pos => rw [hSame i hi hp, hV, mul_one]
    case neg =>
      have hz : a i = 0 := le_antisymm (le_of_not_gt hp) (ha i hi)
      simp [hz]
  case right =>
    unfold thresholdSelectedMass
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : 0 < a i
    case pos =>
      rw [hSame i hi hp, hV]
      simp only [momentRoundIndicator, if_pos hd.le, mul_one]
    case neg =>
      have hz : a i = 0 := le_antisymm (le_of_not_gt hp) (ha i hi)
      simp [hz]

theorem finiteWeighted_one_radius_rigid {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : d < 1)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hCard : (thresholdRadialSupport S a y).card <= 1) :
    And (Finset.sum S (fun i => a i * y i) = Finset.sum S a)
      (thresholdSelectedMass d S a y = Finset.sum S a) := by
  choose i hi using finiteWeightedThreshold_witness S a y d hd ha hy hMoment hMass
  have hMi := (thresholdRadialSupport_mem S a y (y i)).mpr
    (Exists.intro i (And.intro hi.1 (And.intro hi.2.1 rfl)))
  have hSame : forall j, Membership.mem S j -> 0 < a j -> y j = y i := by
    intro j hj hp
    have hMj := (thresholdRadialSupport_mem S a y (y j)).mpr
      (Exists.intro j (And.intro hj (And.intro hp rfl)))
    exact Finset.card_le_one.mp hCard (y j) hMj (y i) hMi
  exact finiteWeighted_constant_radius_rigid S a y d (y i) hd ha hMoment hMass hSame

end PrimeFactorOscillations
