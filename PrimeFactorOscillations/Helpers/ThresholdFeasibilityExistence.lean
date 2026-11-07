/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdFeasibilityModels

/-! # Complete feasible mass region, with two atoms sufficient -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem thresholdEven_exists_bounded (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k)
    (hLow : thresholdMinimumMass d (2 * (k : Real)) <= M) (hHigh : M <= 2 * (k : Real)) :
    exists a : Fin 2 -> Nat, exists y : Fin 2 -> Real,
      thresholdEvenAdmissible d M (2 * (k : Real)) a y := by
  let m := k - 1
  have hCast : (m : Real) = (k : Real) - 1 := by
    dsimp [m]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk.ne')]
    norm_num
  have hCount : 2 * (m : Real) + 2 * (1 : Real) = 2 * (k : Real) := by
    rw [hCast]
    ring
  have hLeft : thresholdModelMass (m : Real) 1 d = thresholdMinimumMass d (2 * (k : Real)) :=
    thresholdModelMass_minimum d k hk
  have hRight : thresholdModelMass (m : Real) 1 1 = 2 * (k : Real) := by
    rw [thresholdModelMass_one]
    exact hCount
  have hBetween : Membership.mem (Set.Icc (thresholdModelMass (m : Real) 1 d)
      (thresholdModelMass (m : Real) 1 1)) M := by
    rw [hLeft, hRight]
    exact And.intro hLow hHigh
  choose u hu using intermediate_value_Icc hd.2.le
    (thresholdModelMass_continuous (m : Real) 1).continuousOn hBetween
  have hAd := thresholdModel_all_selected d u m 1 hd (by decide) hu.1
  simp only [Nat.cast_one] at hAd
  rw [hu.2, hCount] at hAd
  exact Exists.intro (thresholdPairWeights m 1)
    (Exists.intro (thresholdPairCoords u (thresholdModelHigh (m : Real) 1 u)) hAd)

theorem thresholdEven_exists_unbounded (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hLow : 2 * (k : Real) <= M) :
    exists a : Fin 2 -> Nat, exists y : Fin 2 -> Real,
      thresholdEvenAdmissible d M (2 * (k : Real)) a y := by
  choose n hn using exists_nat_gt (M / d)
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hCancel : d * (M / d) = M := by field_simp [hd.1.ne']
  have hND : M < (n : Real) * d := by
    have hp := mul_pos (sub_pos.mpr hn) hd.1
    nlinarith only [hp, hCancel]
  have hU : And (0 <= d / 2) (d / 2 <= 1) := by constructor <;> linarith [hd.1, hd.2]
  have hLarge := thresholdModelMass_lower (n : Real) (k : Real) (d / 2)
    (Nat.cast_nonneg n) hkR hU
  have hRight : M <= thresholdModelMass (n : Real) (k : Real) (d / 2) := by
    nlinarith only [hLarge, hND, hkR]
  have hBetween : Membership.mem (Set.Icc (thresholdModelMass (n : Real) (k : Real) 0)
      (thresholdModelMass (n : Real) (k : Real) (d / 2))) M := by
    rw [thresholdModelMass_zero]
    exact And.intro hLow hRight
  choose u hu using intermediate_value_Icc hU.1
    (thresholdModelMass_continuous (n : Real) (k : Real)).continuousOn hBetween
  have huCut : And (0 <= u) (And (u < d) (u <= 1)) := by
    exact And.intro hu.1.1 (And.intro (by linarith [hu.1.2, hd.1])
      (le_trans hu.1.2 hU.2))
  have hAd := thresholdModel_high_selected d u n k hd hk huCut
  rw [hu.2] at hAd
  exact Exists.intro (thresholdPairWeights n k)
    (Exists.intro (thresholdPairCoords u (thresholdModelHigh (n : Real) (k : Real) u)) hAd)

theorem thresholdEven_two_atom_feasibility (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) :
    (exists a : Fin 2 -> Nat, exists y : Fin 2 -> Real,
      thresholdEvenAdmissible d M (2 * (k : Real)) a y) <->
      thresholdMinimumMass d (2 * (k : Real)) <= M := by
  have hkR : (1 : Real) <= (k : Real) := by exact_mod_cast hk
  have hK : 2 <= 2 * (k : Real) := by linarith only [hkR]
  constructor
  case mp =>
    intro h
    choose a y hAd using h
    exact thresholdEvenAdmissible_mass_floor d M (2 * (k : Real)) a y hd hK hAd
  case mpr =>
    intro h
    by_cases hHigh : M <= 2 * (k : Real)
    case pos => exact thresholdEven_exists_bounded d M k hd hk h hHigh
    case neg => exact thresholdEven_exists_unbounded d M k hd hk (le_of_not_ge hHigh)

theorem thresholdEven_finite_feasibility (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) :
    (exists n : Nat, exists a : Fin n -> Nat, exists y : Fin n -> Real,
      thresholdEvenAdmissible d M (2 * (k : Real)) a y) <->
      thresholdMinimumMass d (2 * (k : Real)) <= M := by
  constructor
  case mp =>
    intro h
    choose n a y hAd using h
    have hkR : (1 : Real) <= (k : Real) := by exact_mod_cast hk
    exact thresholdEvenAdmissible_mass_floor d M (2 * (k : Real)) a y hd
      (by linarith only [hkR]) hAd
  case mpr =>
    intro h
    choose a y hAd using (thresholdEven_two_atom_feasibility d M k hd hk).mpr h
    exact Exists.intro 2 (Exists.intro a (Exists.intro y hAd))

theorem thresholdEven_minimum_attained (d : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) :
    exists a : Fin 2 -> Nat, exists y : Fin 2 -> Real,
      thresholdEvenAdmissible d (thresholdMinimumMass d (2 * (k : Real)))
        (2 * (k : Real)) a y := by
  exact (thresholdEven_two_atom_feasibility d (thresholdMinimumMass d (2 * (k : Real))) k hd hk).mpr le_rfl

end PrimeFactorOscillations
