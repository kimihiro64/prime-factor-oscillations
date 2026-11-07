/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Topology.Order.IntermediateValue
import PrimeFactorOscillations.Helpers.NegativeThresholdSharpness
import PrimeFactorOscillations.Helpers.ThresholdFeasibilityRoot

/-! # Continuous two-atom equal-moment constructions -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdModelHigh (m n u : Real) : Real :=
  (1 + Real.sqrt (1 + 4 * (m / n) * u * (1 - u))) / 2

def thresholdModelMass (m n u : Real) : Real :=
  2 * m * u + 2 * n * thresholdModelHigh m n u

theorem thresholdModelHigh_bounds (m n u : Real) (hm : 0 <= m) (hn : 0 < n)
    (hu : And (0 <= u) (u <= 1)) : 1 <= thresholdModelHigh m n u := by
  have hp := mul_nonneg (mul_nonneg (div_nonneg hm hn.le) hu.1)
    (sub_nonneg.mpr hu.2)
  have hD : 0 <= 1 + 4 * (m / n) * u * (1 - u) := by nlinarith only [hp]
  have hS := Real.sqrt_nonneg (1 + 4 * (m / n) * u * (1 - u))
  have hSq := Real.sq_sqrt hD
  unfold thresholdModelHigh
  nlinarith only [hp, hS, hSq]

theorem thresholdModelHigh_moment (m n u : Real) (hm : 0 <= m) (hn : 0 < n)
    (hu : And (0 <= u) (u <= 1)) :
    m * u ^ 2 + n * (thresholdModelHigh m n u) ^ 2 =
      m * u + n * thresholdModelHigh m n u := by
  have hp := mul_nonneg (mul_nonneg (div_nonneg hm hn.le) hu.1)
    (sub_nonneg.mpr hu.2)
  have hD : 0 <= 1 + 4 * (m / n) * u * (1 - u) := by nlinarith only [hp]
  have hSq := Real.sq_sqrt hD
  have hV : (thresholdModelHigh m n u) ^ 2 - thresholdModelHigh m n u =
      (m / n) * u * (1 - u) := by
    unfold thresholdModelHigh
    nlinarith only [hSq]
  have hBalance : n * ((thresholdModelHigh m n u) ^ 2 - thresholdModelHigh m n u) =
      m * u * (1 - u) := by
    rw [hV]
    field_simp [hn.ne']
  nlinarith only [hBalance]

theorem thresholdModelMass_continuous (m n : Real) : Continuous (thresholdModelMass m n) := by
  unfold thresholdModelMass thresholdModelHigh
  fun_prop

theorem thresholdModelMass_zero (m n : Real) : thresholdModelMass m n 0 = 2 * n := by
  simp [thresholdModelMass, thresholdModelHigh]

theorem thresholdModelMass_one (m n : Real) : thresholdModelMass m n 1 = 2 * m + 2 * n := by
  simp [thresholdModelMass, thresholdModelHigh]

theorem thresholdModelMass_lower (m n u : Real) (hm : 0 <= m) (hn : 0 < n)
    (hu : And (0 <= u) (u <= 1)) :
    2 * m * u + 2 * n <= thresholdModelMass m n u := by
  have hh := thresholdModelHigh_bounds m n u hm hn hu
  have hp := mul_nonneg hn.le (sub_nonneg.mpr hh)
  unfold thresholdModelMass
  nlinarith only [hp]

theorem thresholdPair_admissible (d u v : Real) (m n : Nat)
    (hu : 0 <= u) (hv : 0 <= v)
    (hMoment : (m : Real) * u ^ 2 + (n : Real) * v ^ 2 = (m : Real) * u + (n : Real) * v) :
    thresholdEvenAdmissible d (2 * (m : Real) * u + 2 * (n : Real) * v)
      (2 * (m : Real) * momentRoundIndicator d u + 2 * (n : Real) * momentRoundIndicator d v)
      (thresholdPairWeights m n) (thresholdPairCoords u v) := by
  constructor
  case left =>
    intro i
    unfold thresholdPairCoords
    split_ifs <;> assumption
  case right =>
    constructor
    case left => exact thresholdPair_sum m n u v (fun q => q)
    case right =>
      constructor
      case left =>
        rw [thresholdPair_sum m n u v (fun q => q ^ 2)]
        nlinarith only [hMoment]
      case right =>
        unfold thresholdSelectedMass
        exact thresholdPair_sum m n u v (fun q => momentRoundIndicator d q)

theorem thresholdModel_all_selected (d u : Real) (m n : Nat)
    (hd : And (0 < d) (d < 1)) (hn : 0 < n) (hu : And (d <= u) (u <= 1)) :
    thresholdEvenAdmissible d (thresholdModelMass (m : Real) (n : Real) u)
      (2 * (m : Real) + 2 * (n : Real)) (thresholdPairWeights m n)
      (thresholdPairCoords u (thresholdModelHigh (m : Real) (n : Real) u)) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hu0 : 0 <= u := le_trans hd.1.le hu.1
  have hV := thresholdModelHigh_bounds (m : Real) (n : Real) u (Nat.cast_nonneg m) hnR
    (And.intro hu0 hu.2)
  have hvCut : d <= thresholdModelHigh (m : Real) (n : Real) u := le_trans hd.2.le hV
  have h := thresholdPair_admissible d u (thresholdModelHigh (m : Real) (n : Real) u) m n hu0
    (by linarith only [hV])
    (thresholdModelHigh_moment (m : Real) (n : Real) u (Nat.cast_nonneg m) hnR (And.intro hu0 hu.2))
  simpa only [thresholdModelMass, momentRoundIndicator, if_pos hu.1, if_pos hvCut, mul_one] using h

theorem thresholdModel_high_selected (d u : Real) (m n : Nat)
    (hd : And (0 < d) (d < 1)) (hn : 0 < n)
    (hu : And (0 <= u) (And (u < d) (u <= 1))) :
    thresholdEvenAdmissible d (thresholdModelMass (m : Real) (n : Real) u)
      (2 * (n : Real)) (thresholdPairWeights m n)
      (thresholdPairCoords u (thresholdModelHigh (m : Real) (n : Real) u)) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hV := thresholdModelHigh_bounds (m : Real) (n : Real) u (Nat.cast_nonneg m) hnR
    (And.intro hu.1 hu.2.2)
  have hvCut : d <= thresholdModelHigh (m : Real) (n : Real) u := le_trans hd.2.le hV
  have hCut : Not (d <= u) := not_le.mpr hu.2.1
  have h := thresholdPair_admissible d u (thresholdModelHigh (m : Real) (n : Real) u) m n hu.1
    (by linarith only [hV])
    (thresholdModelHigh_moment (m : Real) (n : Real) u (Nat.cast_nonneg m) hnR (And.intro hu.1 hu.2.2))
  simpa only [thresholdModelMass, momentRoundIndicator, if_neg hCut, if_pos hvCut, mul_zero,
    mul_one, zero_add] using h

theorem thresholdModelMass_minimum (d : Real) (k : Nat) (hk : 0 < k) :
    thresholdModelMass ((k - 1 : Nat) : Real) 1 d = thresholdMinimumMass d (2 * (k : Real)) := by
  have hCast : ((k - 1 : Nat) : Real) = (k : Real) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk.ne')]
    norm_num
  have hRad : 1 + 4 * (((k - 1 : Nat) : Real) / 1) * d * (1 - d) =
      1 + 2 * (2 * (k : Real) - 2) * d * (1 - d) := by rw [hCast]; ring
  unfold thresholdModelMass thresholdModelHigh thresholdMinimumMass
  rw [hRad, hCast]
  ring

end PrimeFactorOscillations
