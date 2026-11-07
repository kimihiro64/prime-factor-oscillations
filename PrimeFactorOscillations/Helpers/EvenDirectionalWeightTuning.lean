/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Topology.Order.IntermediateValue
import PrimeFactorOscillations.Helpers.DirectionalParityOptimality

/-! # Exact reciprocal-weight tuning for positive parity models -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem positiveParityWeight_zero : positiveParityWeight 0 = 0 := by
  simp [positiveParityWeight, positiveParityHigh]

theorem positiveParityWeight_continuousOn (r : Real)
    (hr : And (0 < r) (r < 1 / 2)) :
    ContinuousOn positiveParityWeight (Set.Icc 0 r) := by
  intro e he
  have heHalf : e < 1 / 2 := lt_of_le_of_lt he.2 hr.2
  have hLow : 0 < positiveParityLow e := by
    by_cases hp : 0 < e
    case pos => exact (positiveParityLow_bounds e (And.intro hp heHalf)).1
    case neg =>
      have hz : e = 0 := le_antisymm (le_of_not_gt hp) he.1
      rw [hz]
      simpa [positiveParityLow] using momentRoundThreshold_bounds.1
  have hUpper : positiveParityLow e <= momentRoundThreshold := by
    unfold positiveParityLow
    nlinarith only [sq_nonneg e]
  have hOne : 0 < 1 - positiveParityLow e := by
    have hd := momentRoundThreshold_bounds.2
    linarith only [hUpper, hd]
  have hDen : Not ((momentRoundThreshold - e ^ 2) *
      (1 - (momentRoundThreshold - e ^ 2)) = 0) := by
    change Not (positiveParityLow e * (1 - positiveParityLow e) = 0)
    exact (mul_pos hLow hOne).ne'
  apply ContinuousAt.continuousWithinAt
  unfold positiveParityWeight positiveParityHigh positiveParityLow
  fun_prop (disch := assumption)

theorem positiveParityWeight_reciprocal (r : Real)
    (hr : And (0 < r) (r < 1 / 2)) (n : Nat) (hn : 0 < n)
    (hLarge : 1 / positiveParityWeight r < (n : Real)) :
    exists e : Real, And (And (0 < e) (e <= r))
      ((2 * (n : Real)) * positiveParityWeight e = 2) := by
  have hWr := positiveParityWeight_pos r hr
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  have hCancelW : (1 / positiveParityWeight r) * positiveParityWeight r = 1 := by
    field_simp [hWr.ne']
  have hGap := mul_pos (sub_pos.mpr hLarge) hWr
  have hProduct : 1 < (n : Real) * positiveParityWeight r := by
    nlinarith only [hGap, hCancelW]
  have hQ : 0 < (1 : Real) / (n : Real) := div_pos (by norm_num) hN
  have hCancelN : ((1 : Real) / (n : Real)) * (n : Real) = 1 := by
    field_simp [hN.ne']
  have hQUpper : (1 : Real) / (n : Real) <= positiveParityWeight r := by
    by_contra hh
    have hm := mul_pos (sub_pos.mpr (lt_of_not_ge hh)) hN
    nlinarith only [hm, hCancelN, hProduct]
  have hBetween : Membership.mem (Set.Icc (positiveParityWeight 0) (positiveParityWeight r))
      ((1 : Real) / (n : Real)) := by
    rw [positiveParityWeight_zero]
    exact And.intro hQ.le hQUpper
  have hImage := intermediate_value_Icc hr.1.le (positiveParityWeight_continuousOn r hr) hBetween
  choose e he using hImage
  have hePos : 0 < e := by
    by_contra hh
    have heZero : e = 0 := le_antisymm (le_of_not_gt hh) he.1.1
    have heWeight := he.2
    rw [heZero, positiveParityWeight_zero] at heWeight
    linarith only [heWeight, hQ]
  refine Exists.intro e (And.intro (And.intro hePos he.1.2) ?_)
  rw [he.2]
  field_simp [hN.ne']

theorem positiveParityWeight_integral_scales (c : Real) (hc : positiveParityCoefficient < c) :
    exists N : Nat, And (0 < N) (forall n : Nat, N <= n ->
      exists e : Real, And (And (0 < e) (e < 1 / 2))
        (And ((2 * (n : Real)) * positiveParityWeight e = 2) (positiveParityRatio e < c))) := by
  choose radius hRadius hClose using
    (Metric.continuousAt_iff.mp positiveParityRatio_continuousAt_zero)
      (c - positiveParityCoefficient) (sub_pos.mpr hc)
  let r := min (radius / 2) (1 / 4)
  have hrPos : 0 < r := lt_min (by linarith) (by norm_num)
  have hrHalf : r < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrRadius : r < radius := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  choose N hN using exists_nat_gt (max (1 : Real) (1 / positiveParityWeight r))
  have hNReal : 0 < (N : Real) := lt_trans (by norm_num)
    (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNPos : 0 < N := by exact_mod_cast hNReal
  refine Exists.intro N (And.intro hNPos ?_)
  intro n hn
  have hNn : (N : Real) <= (n : Real) := by exact_mod_cast hn
  have hnPos : 0 < n := lt_of_lt_of_le hNPos hn
  have hLarge : 1 / positiveParityWeight r < (n : Real) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hNn
  choose e he using positiveParityWeight_reciprocal r (And.intro hrPos hrHalf) n hnPos hLarge
  have heHalf : e < 1 / 2 := lt_of_le_of_lt he.1.2 hrHalf
  have heRadius : e < radius := lt_of_le_of_lt he.1.2 hrRadius
  have hDist : dist e 0 < radius := by
    rw [Real.dist_eq, sub_zero, abs_of_pos he.1.1]
    exact heRadius
  have hNear := hClose hDist
  rw [positiveParityRatio_zero, Real.dist_eq] at hNear
  have hRlt : positiveParityRatio e < c := by
    have hh := (abs_lt.mp hNear).2
    linarith only [hh]
  exact Exists.intro e (And.intro (And.intro he.1.1 heHalf) (And.intro he.2 hRlt))

end PrimeFactorOscillations
