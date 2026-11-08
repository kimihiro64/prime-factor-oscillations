/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FinCases
import PrimeFactorOscillations.Helpers.ThresholdSingleLevelSharpness

/-! # Fixed even-mass threshold profiles from a selected rational rotation -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdRotationCenter (a q : Real) : Real :=
  a - (2 * a - 1) * q ^ 2 / (1 + q ^ 2)

def thresholdRotationRadius (a q : Real) : Real :=
  (2 * a - 1) * q / (1 + q ^ 2)

theorem thresholdRotation_moment (a q : Real) :
    (thresholdRotationCenter a q) ^ 2 + (thresholdRotationRadius a q) ^ 2 -
      thresholdRotationCenter a q = a ^ 2 - a := by
  have hn : Not (1 + q ^ 2 = 0) := by nlinarith only [sq_nonneg q]
  unfold thresholdRotationCenter thresholdRotationRadius
  field_simp [hn]
  ring

theorem thresholdRotation_radius_lower (a q : Real) (ha : 1 <= a)
    (hq : And (0 <= q) (q <= 1)) : q / 2 <= thresholdRotationRadius a q := by
  have hden : 0 < 1 + q ^ 2 := by nlinarith only [sq_nonneg q]
  have hNum : 0 <= (2 * a - 1) * q :=
    mul_nonneg (by linarith only [ha]) hq.1
  have hR : 0 <= thresholdRotationRadius a q := div_nonneg hNum hden.le
  have hId : thresholdRotationRadius a q * (1 + q ^ 2) = (2 * a - 1) * q := by
    unfold thresholdRotationRadius
    field_simp [hden.ne']
  have hQ : q ^ 2 <= 1 := by nlinarith only [hq.1, hq.2]
  have hRest := mul_nonneg hR (sub_nonneg.mpr hQ)
  have hGain := mul_nonneg hq.1 (show 0 <= 2 * a - 2 by linarith only [ha])
  nlinarith only [hId, hRest, hGain]

def thresholdEvenSplitHigh (m k : Nat) (d q : Real) : Real :=
  thresholdSingleFamilyHigh (2 * (m : Real)) (2 * (k : Real)) d (q ^ 2)

def thresholdEvenSplitOrder (m k : Nat) : Fin 4 -> Nat := ![m, 1, 1, k - 2]

def thresholdEvenSplitCoord (m k : Nat) (d q : Real) : Fin 4 -> Real :=
  ![d - q ^ 2,
    thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q +
      thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q,
    thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q -
      thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q,
    thresholdEvenSplitHigh m k d q]

def thresholdEvenSplitGap (m k : Nat) (d q : Real) : Real :=
  thresholdSingleFamilyGap (2 * (m : Real)) (2 * (k : Real)) d (q ^ 2) +
    4 * (2 * thresholdEvenSplitHigh m k d q - 1) * q ^ 2 / (1 + q ^ 2)

theorem thresholdEvenSplit_sum (m k : Nat) (d q : Real) (phi : Real -> Real) :
    Finset.sum Finset.univ (fun i => 2 * (thresholdEvenSplitOrder m k i : Real) *
      phi (thresholdEvenSplitCoord m k d q i)) =
      2 * (m : Real) * phi (d - q ^ 2) +
        2 * phi (thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q +
          thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q) +
        2 * phi (thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q -
          thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q) +
        2 * ((k - 2 : Nat) : Real) * phi (thresholdEvenSplitHigh m k d q) := by
  norm_num [Fin.sum_univ_succ, thresholdEvenSplitOrder, thresholdEvenSplitCoord]
  ring

theorem thresholdEvenSplit_total (m k : Nat) (hk : 2 <= k) :
    Finset.sum Finset.univ (fun i => 2 * (thresholdEvenSplitOrder m k i : Real)) =
      2 * (m : Real) + 2 * (k : Real) := by
  have hh := thresholdEvenSplit_sum m k 0 0 (fun _ => (1 : Real))
  simp only [mul_one] at hh
  rw [hh, Nat.cast_sub hk]
  norm_num
  ring

theorem thresholdEvenSplit_first (m k : Nat) (d q : Real) (hk : 2 <= k) :
    Finset.sum Finset.univ (fun i => 2 * (thresholdEvenSplitOrder m k i : Real) *
      thresholdEvenSplitCoord m k d q i) =
      thresholdTotalUpper d (2 * (m : Real) + 2 * (k : Real)) (2 * (k : Real)) -
        thresholdEvenSplitGap m k d q := by
  rw [thresholdEvenSplit_sum m k d q (fun z => z), Nat.cast_sub hk]
  unfold thresholdTotalUpper thresholdEvenSplitGap thresholdSingleFamilyGap
  rw [show 2 * (m : Real) + 2 * (k : Real) - 2 * (k : Real) = 2 * (m : Real) by ring]
  dsimp only [thresholdEvenSplitHigh, thresholdRotationCenter]
  norm_num
  ring

theorem thresholdEvenSplit_equal_moments (m k : Nat) (d q : Real) (hk : 2 <= k)
    (hd : And (0 < d) (d < 1)) (hqd : q ^ 2 < d) :
    Finset.sum Finset.univ (fun i => 2 * (thresholdEvenSplitOrder m k i : Real) *
      (thresholdEvenSplitCoord m k d q i) ^ 2) =
      Finset.sum Finset.univ (fun i => 2 * (thresholdEvenSplitOrder m k i : Real) *
        thresholdEvenSplitCoord m k d q i) := by
  have hkR : (2 : Real) <= (k : Real) := by exact_mod_cast hk
  have hBase := thresholdModelHigh_moment (2 * (m : Real)) (2 * (k : Real)) (d - q ^ 2)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg m)) (by linarith only [hkR])
    (And.intro (sub_nonneg.mpr hqd.le) (by nlinarith only [hd.2, sq_nonneg q]))
  have hRot := thresholdRotation_moment (thresholdEvenSplitHigh m k d q) q
  rw [thresholdEvenSplit_sum m k d q (fun z => z ^ 2),
    thresholdEvenSplit_sum m k d q (fun z => z), Nat.cast_sub hk]
  change 2 * (m : Real) * (d - q ^ 2) ^ 2 +
      2 * (thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q +
        thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q) ^ 2 +
      2 * (thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q -
        thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q) ^ 2 +
      2 * ((k : Real) - (2 : Real)) * (thresholdEvenSplitHigh m k d q) ^ 2 = _
  change 2 * (m : Real) * (d - q ^ 2) ^ 2 +
      2 * (k : Real) * (thresholdEvenSplitHigh m k d q) ^ 2 =
      2 * (m : Real) * (d - q ^ 2) + 2 * (k : Real) * thresholdEvenSplitHigh m k d q at hBase
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hBase, hRot]

theorem thresholdEvenSplit_high_bounds (m k : Nat) (d q : Real)
    (hk : 2 <= k) (hd : And (0 < d) (d < 1)) (hqd : q ^ 2 < d) :
    And (1 <= thresholdEvenSplitHigh m k d q)
      (4 * thresholdEvenSplitHigh m k d q <= 2 * (m : Real) + 4) := by
  let J := 2 * (m : Real)
  let K := 2 * (k : Real)
  let u := d - q ^ 2
  let a := thresholdEvenSplitHigh m k d q
  have hJ : 0 <= J := mul_nonneg (by norm_num) (Nat.cast_nonneg m)
  have hkR : (2 : Real) <= (k : Real) := by exact_mod_cast hk
  have hK : 4 <= K := by dsimp only [K]; linarith only [hkR]
  have hu : And (0 <= u) (u <= 1) :=
    And.intro (sub_nonneg.mpr hqd.le) (by dsimp only [u]; nlinarith only [hd.2, sq_nonneg q])
  have ha : 1 <= a := thresholdModelHigh_bounds J K u hJ (by linarith only [hK]) hu
  have hBase : J * u ^ 2 + K * a ^ 2 = J * u + K * a :=
    thresholdModelHigh_moment J K u hJ (by linarith only [hK]) hu
  have hJu := mul_nonneg hJ (sub_nonneg.mpr hu.2)
  have hJu2 := mul_nonneg hJ (sq_nonneg u)
  have hSquare := mul_nonneg (show 0 <= K by linarith only [hK]) (sq_nonneg (a - 1))
  have hCompare := mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr ha)
  refine And.intro ha ?_
  change 4 * a <= J + 4
  nlinarith only [hBase, hJu, hJu2, hSquare, hCompare]

theorem thresholdEvenSplit_gap_bounds (m k : Nat) (d q : Real)
    (hk : 2 <= k) (hd : And (0 < d) (d < 1)) (hq : 0 < q) (hqd : q ^ 2 < d) :
    And (0 < thresholdEvenSplitGap m k d q)
      (thresholdEvenSplitGap m k d q <= (8 * (m : Real) + 4) * q ^ 2) := by
  let J := 2 * (m : Real)
  let K := 2 * (k : Real)
  let a := thresholdEvenSplitHigh m k d q
  let oldGap := thresholdSingleFamilyGap J K d (q ^ 2)
  let correction := 4 * (2 * a - 1) * q ^ 2 / (1 + q ^ 2)
  have hkR : (2 : Real) <= (k : Real) := by exact_mod_cast hk
  have hK : 0 < K := by dsimp only [K]; linarith only [hkR]
  have hHigh := thresholdEvenSplit_high_bounds m k d q hk hd hqd
  have hOld : And (0 <= oldGap) (oldGap <= 2 * J * q ^ 2) := by
    by_cases hm : m = 0
    case pos =>
      subst m
      norm_num [oldGap, J, thresholdSingleFamilyGap, thresholdSingleFamilyHigh, thresholdModelHigh]
    case neg =>
      have hmR : (0 : Real) < (m : Real) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
      have hh := thresholdSingleFamily_gap_bounds J K d (q ^ 2)
        (mul_pos (by norm_num) hmR) hK hd (And.intro (sq_pos_of_pos hq) hqd)
      exact And.intro hh.1.le hh.2
  have hDen : 0 < 1 + q ^ 2 := by nlinarith only [sq_nonneg q]
  have hNum : 0 < 4 * (2 * a - 1) * q ^ 2 :=
    mul_pos (mul_pos (by norm_num) (by linarith only [hHigh.1])) (sq_pos_of_pos hq)
  have hCorrection : 0 < correction := div_pos hNum hDen
  have hIdentity : correction * (1 + q ^ 2) = 4 * (2 * a - 1) * q ^ 2 := by
    dsimp only [correction]
    field_simp [hDen.ne']
  have hExtra := mul_nonneg hCorrection.le (sq_nonneg q)
  have hCoeff : 4 * (2 * a - 1) <= 2 * J + 4 := by
    dsimp only [a, J]
    linarith only [hHigh.2]
  have hBound := mul_le_mul_of_nonneg_right hCoeff (sq_nonneg q)
  have hGap : thresholdEvenSplitGap m k d q = oldGap + correction := rfl
  rw [hGap]
  refine And.intro (by linarith only [hOld.1, hCorrection]) ?_
  rw [show 8 * (m : Real) + 4 = 4 * J + 4 by dsimp only [J]; ring]
  nlinarith only [hOld.2, hIdentity, hExtra, hBound]

theorem thresholdEvenSplit_window (m k : Nat) (d : Real) (hk : 2 <= k)
    (hd : And (0 < d) (d < 1)) :
    exists r : Real, And (0 < r) (forall q : Real, And (0 < q) (q < r) ->
      And (q < 1) (And (q ^ 2 < d)
        (And (d <= thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q +
            thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q)
          (d <= thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q -
            thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q)))) := by
  let v := thresholdModelHigh (2 * (m : Real)) (2 * (k : Real)) d
  let plus := fun q : Real => thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q +
    thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q
  let minus := fun q : Real => thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q -
    thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q
  have hkR : (2 : Real) <= (k : Real) := by exact_mod_cast hk
  have hv : 1 <= v := thresholdModelHigh_bounds _ _ d
    (mul_nonneg (by norm_num) (Nat.cast_nonneg m)) (by linarith only [hkR])
    (And.intro hd.1.le hd.2.le)
  have hHigh : Continuous (thresholdEvenSplitHigh m k d) := by
    unfold thresholdEvenSplitHigh thresholdSingleFamilyHigh thresholdModelHigh
    fun_prop
  have hDen : ContinuousAt (fun q : Real => 1 + q ^ 2) 0 := by fun_prop
  have hNum : ContinuousAt (fun q : Real => 2 * thresholdEvenSplitHigh m k d q - 1) 0 :=
    (continuousAt_const.mul hHigh.continuousAt).sub continuousAt_const
  have hShift := (hNum.mul (continuousAt_id.pow 2)).div hDen (by norm_num)
  have hRad := (hNum.mul continuousAt_id).div hDen (by norm_num)
  have hpCont : ContinuousAt plus 0 := (hHigh.continuousAt.sub hShift).add hRad
  have hmCont : ContinuousAt minus 0 := (hHigh.continuousAt.sub hShift).sub hRad
  have hpZero : plus 0 = v := by
    simp [plus, thresholdRotationCenter, thresholdRotationRadius, thresholdEvenSplitHigh,
      thresholdSingleFamilyHigh, v]
  have hmZero : minus 0 = v := by
    simp [minus, thresholdRotationCenter, thresholdRotationRadius, thresholdEvenSplitHigh,
      thresholdSingleFamilyHigh, v]
  have hpEvent : Filter.Eventually (fun q : Real => d < plus q) (nhds 0) :=
    hpCont.tendsto.eventually (Ioi_mem_nhds (by rw [hpZero]; linarith only [hv, hd.2]))
  have hmEvent : Filter.Eventually (fun q : Real => d < minus q) (nhds 0) :=
    hmCont.tendsto.eventually (Ioi_mem_nhds (by rw [hmZero]; linarith only [hv, hd.2]))
  choose rp hrp hbp using Metric.mem_nhds_iff.mp hpEvent
  choose rm hrm hbm using Metric.mem_nhds_iff.mp hmEvent
  let r := min (d / 2) (min (1 / 4) (min rp rm))
  have hr : 0 < r := lt_min (div_pos hd.1 (by norm_num))
    (lt_min (by norm_num) (lt_min hrp hrm))
  refine Exists.intro r (And.intro hr ?_)
  intro q hq
  have hqd2 : q < d / 2 := lt_of_lt_of_le hq.2 (min_le_left _ _)
  have hq4 : q < 1 / 4 := lt_of_lt_of_le hq.2
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hqp : q < rp := lt_of_lt_of_le hq.2
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hqm : q < rm := lt_of_lt_of_le hq.2
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hP := hbp (show Membership.mem (Metric.ball (0 : Real) rp) q by
    change dist q 0 < rp
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hq.1] using hqp)
  have hM := hbm (show Membership.mem (Metric.ball (0 : Real) rm) q by
    change dist q 0 < rm
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hq.1] using hqm)
  have hSquare : q ^ 2 <= q := by nlinarith only [hq.1, hq4]
  exact And.intro (by linarith only [hq4])
    (And.intro (by linarith only [hSquare, hqd2, hd.1]) (And.intro hP.le hM.le))

theorem thresholdEvenSplit_admissible (m k : Nat) (d q : Real) (hk : 2 <= k)
    (hd : And (0 < d) (d < 1)) (hqd : And (0 < q) (q ^ 2 < d))
    (hPlus : d <= thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q +
      thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q)
    (hMinus : d <= thresholdRotationCenter (thresholdEvenSplitHigh m k d q) q -
      thresholdRotationRadius (thresholdEvenSplitHigh m k d q) q) :
    thresholdTotalAdmissible d
      (thresholdTotalUpper d (2 * (m : Real) + 2 * (k : Real)) (2 * (k : Real)) -
        thresholdEvenSplitGap m k d q) (2 * (m : Real) + 2 * (k : Real)) (2 * (k : Real))
      (thresholdEvenSplitOrder m k) (thresholdEvenSplitCoord m k d q) := by
  have hHigh := thresholdEvenSplit_high_bounds m k d q hk hd hqd.2
  have hLow : d - q ^ 2 < d := by nlinarith only [sq_pos_of_pos hqd.1]
  have hBase : d <= thresholdEvenSplitHigh m k d q := by linarith only [hHigh.1, hd.2]
  have hFirst := thresholdEvenSplit_first m k d q hk
  have hSecond := (thresholdEvenSplit_equal_moments m k d q hk hd hqd.2).trans hFirst
  refine And.intro (thresholdEvenSplit_total m k hk)
    (And.intro ?_ (And.intro hFirst (And.intro hSecond ?_)))
  next =>
    intro i
    fin_cases i <;> norm_num [thresholdEvenSplitCoord]
    all_goals linarith only [hqd.2, hPlus, hMinus, hBase, hd.1]
  next =>
    unfold thresholdSelectedMass
    rw [thresholdEvenSplit_sum m k d q (momentRoundIndicator d)]
    simp only [momentRoundIndicator, ite_eq_right (not_le.mpr hLow),
      ite_eq_left hPlus, ite_eq_left hMinus, ite_eq_left hBase,
      mul_zero, zero_add, mul_one]
    rw [Nat.cast_sub hk]
    norm_num
    ring

end PrimeFactorOscillations
