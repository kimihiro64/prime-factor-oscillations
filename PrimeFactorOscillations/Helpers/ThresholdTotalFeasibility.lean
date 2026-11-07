/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdTotalModels

/-! # Complete fixed-total threshold feasibility, including both upper faces -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem thresholdTotalAdmissible_region {r : Nat} (d M : Real) (n k : Nat)
    (a : Fin r -> Nat) (y : Fin r -> Real)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hkn : k <= n)
    (hAd : thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y) :
    And (thresholdMinimumMass d (2 * (k : Real)) <= M)
      (if n = k then M <= 2 * (k : Real)
       else M < thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real))) := by
  have hkR : (1 : Real) <= (k : Real) := by exact_mod_cast hk
  constructor
  case left =>
    exact thresholdEvenAdmissible_mass_floor d M (2 * (k : Real)) a y hd
      (by linarith only [hkR]) hAd.2
  case right =>
    by_cases heq : n = k
    case pos =>
      simp only [if_pos heq]
      have h := thresholdEvenAdmissible_le_total d M (2 * (n : Real)) (2 * (k : Real)) a y hAd.1 hAd.2
      simpa only [heq] using h
    case neg =>
      simp only [if_neg heq]
      have hknStrict : k < n := by omega
      have hknR : (k : Real) < (n : Real) := by exact_mod_cast hknStrict
      exact thresholdEvenAdmissible_total_upper d M (2 * (n : Real)) (2 * (k : Real)) a y hd
        (by linarith only [hkR]) (by linarith only [hknR]) hAd.1 hAd.2

theorem thresholdTotal_three_site_feasibility (d M : Real) (n k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hkn : k <= n) :
    (exists a : Fin 3 -> Nat, exists y : Fin 3 -> Real,
      thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y) <->
    And (thresholdMinimumMass d (2 * (k : Real)) <= M)
      (if n = k then M <= 2 * (k : Real)
       else M < thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real))) := by
  constructor
  case mp =>
    intro h
    choose a y hAd using h
    exact thresholdTotalAdmissible_region d M n k a y hd hk hkn hAd
  case mpr =>
    intro hRegion
    by_cases hMK : M <= 2 * (k : Real)
    case pos => exact thresholdTotal_exists_bounded d M n k hd hk hkn hRegion.1 hMK
    case neg =>
      have hHigh : M < thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real)) := by
        by_cases heq : n = k
        case pos =>
          have hh := hRegion.2
          simp only [if_pos heq] at hh
          exact False.elim (hMK hh)
        case neg => simpa only [if_neg heq] using hRegion.2
      choose a y hAd using thresholdTotal_exists_upper d M n k hd hk hkn (le_of_not_ge hMK) hHigh
      have hPad := thresholdTotalAdmissible_pad d M (2 * (n : Real)) (2 * (k : Real)) a y 0 hd.1 hAd
      simp only [Nat.cast_zero, mul_zero, zero_add] at hPad
      exact Exists.intro _ (Exists.intro _ hPad)

theorem thresholdTotal_finite_feasibility (d M : Real) (n k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hkn : k <= n) :
    (exists r : Nat, exists a : Fin r -> Nat, exists y : Fin r -> Real,
      thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y) <->
    And (thresholdMinimumMass d (2 * (k : Real)) <= M)
      (if n = k then M <= 2 * (k : Real)
       else M < thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real))) := by
  constructor
  case mp =>
    intro h
    choose r a y hAd using h
    exact thresholdTotalAdmissible_region d M n k a y hd hk hkn hAd
  case mpr =>
    intro h
    choose a y hAd using (thresholdTotal_three_site_feasibility d M n k hd hk hkn).mpr h
    exact Exists.intro 3 (Exists.intro a (Exists.intro y hAd))

theorem thresholdTotal_minimum_attained (d : Real) (n k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hkn : k <= n) :
    exists a : Fin 3 -> Nat, exists y : Fin 3 -> Real,
      thresholdTotalAdmissible d (thresholdMinimumMass d (2 * (k : Real)))
        (2 * (n : Real)) (2 * (k : Real)) a y := by
  have hkR : (1 : Real) <= (k : Real) := by exact_mod_cast hk
  have hBound := (thresholdMinimumMass_bounds d (2 * (k : Real)) hd (by linarith only [hkR])).2.2
  exact thresholdTotal_exists_bounded d (thresholdMinimumMass d (2 * (k : Real))) n k hd hk hkn le_rfl hBound

theorem thresholdTotal_diagonal_upper_attained (d : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) :
    exists a : Fin 3 -> Nat, exists y : Fin 3 -> Real,
      thresholdTotalAdmissible d (2 * (k : Real)) (2 * (k : Real)) (2 * (k : Real)) a y := by
  have hkR : (1 : Real) <= (k : Real) := by exact_mod_cast hk
  have hBound := (thresholdMinimumMass_bounds d (2 * (k : Real)) hd (by linarith only [hkR])).2.2
  exact thresholdTotal_exists_bounded d (2 * (k : Real)) k k hd hk le_rfl hBound le_rfl

theorem thresholdTotal_upper_approximable (d eps : Real) (n k : Nat)
    (hd : And (0 < d) (d < 1)) (heps : 0 < eps) (hk : 0 < k) (hkn : k < n) :
    exists M : Real, exists a : Fin 2 -> Nat, exists y : Fin 2 -> Real,
      And (thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real)) - eps < M)
        (And (M < thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real)))
          (thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y)) := by
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hknR : (k : Real) < (n : Real) := by exact_mod_cast hkn
  let U := thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real))
  have hKU : 2 * (k : Real) < U := (thresholdTotalUpper_open_bounds d (2 * (n : Real))
    (2 * (k : Real)) hd (by linarith only [hkR]) (by linarith only [hknR])).1
  let e := min eps (U - 2 * (k : Real))
  let M := U - e / 2
  have he : 0 < e := lt_min heps (sub_pos.mpr hKU)
  have heE : e <= eps := min_le_left _ _
  have heK : e <= U - 2 * (k : Real) := min_le_right _ _
  have hLow : 2 * (k : Real) <= M := by dsimp [M]; linarith only [heK, hKU]
  have hHigh : M < U := by dsimp [M]; linarith only [he]
  have hClose : U - eps < M := by dsimp [M]; linarith only [heE, heps]
  choose a y hAd using thresholdTotal_exists_upper d M n k hd hk hkn.le hLow hHigh
  exact Exists.intro M (Exists.intro a (Exists.intro y (And.intro hClose (And.intro hHigh hAd))))

end PrimeFactorOscillations
