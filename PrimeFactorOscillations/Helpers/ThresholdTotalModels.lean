/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdTotalBoundary

/-! # Exact total-weight constructions for the full threshold region -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdTotalAdmissible {r : Nat} (d M N K : Real)
    (a : Fin r -> Nat) (y : Fin r -> Real) : Prop :=
  And (Finset.sum Finset.univ (fun i => 2 * (a i : Real)) = N)
    (thresholdEvenAdmissible d M K a y)

def thresholdPadWeights {r : Nat} (q : Nat) (a : Fin r -> Nat) : Fin (r + 1) -> Nat :=
  Fin.cases q a

def thresholdPadCoords {r : Nat} (y : Fin r -> Real) : Fin (r + 1) -> Real :=
  Fin.cases 0 y

theorem thresholdPair_total (m n : Nat) :
    Finset.sum Finset.univ (fun i => 2 * (thresholdPairWeights m n i : Real)) =
      2 * (m : Real) + 2 * (n : Real) := by
  simpa only [mul_one] using thresholdPair_sum m n 0 0 (fun _ => (1 : Real))

theorem thresholdTotalAdmissible_pad {r : Nat} (d M N K : Real)
    (a : Fin r -> Nat) (y : Fin r -> Real) (q : Nat) (hd : 0 < d)
    (hAd : thresholdTotalAdmissible d M N K a y) :
    thresholdTotalAdmissible d M (2 * (q : Real) + N) K
      (thresholdPadWeights q a) (thresholdPadCoords y) := by
  have hZero : momentRoundIndicator d 0 = 0 := by
    simp [momentRoundIndicator, not_le.mpr hd]
  constructor
  case left =>
    simpa [thresholdPadWeights, Fin.sum_univ_succ] using
      congrArg (fun z : Real => 2 * (q : Real) + z) hAd.1
  case right =>
    constructor
    case left =>
      intro i
      exact Fin.cases (by simp [thresholdPadCoords])
        (fun j => by simpa [thresholdPadCoords] using hAd.2.1 j) i
    case right =>
      constructor
      case left =>
        simpa [thresholdPadWeights, thresholdPadCoords, Fin.sum_univ_succ] using hAd.2.2.1
      case right =>
        constructor
        case left =>
          simpa [thresholdPadWeights, thresholdPadCoords, Fin.sum_univ_succ] using hAd.2.2.2.1
        case right =>
          simpa [thresholdSelectedMass, thresholdPadWeights, thresholdPadCoords,
            Fin.sum_univ_succ, hZero] using hAd.2.2.2.2

theorem thresholdTotalUpper_even (d : Real) (n k : Nat) (hk : 0 < k) (hkn : k <= n) :
    thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real)) =
      thresholdModelMass ((n - k : Nat) : Real) (k : Real) d := by
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hJ : 2 * (n : Real) - 2 * (k : Real) = 2 * ((n - k : Nat) : Real) := by
    rw [Nat.cast_sub hkn]
    ring
  have hRatio : (2 * ((n - k : Nat) : Real)) / (2 * (k : Real)) =
      ((n - k : Nat) : Real) / (k : Real) := by
    field_simp [hkR.ne']
  unfold thresholdTotalUpper thresholdModelMass thresholdModelHigh
  rw [hJ, hRatio]

theorem thresholdTotal_exists_bounded (d M : Real) (n k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hkn : k <= n)
    (hLow : thresholdMinimumMass d (2 * (k : Real)) <= M) (hHigh : M <= 2 * (k : Real)) :
    exists a : Fin 3 -> Nat, exists y : Fin 3 -> Real,
      thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y := by
  let m := k - 1
  have hCast : (m : Real) = (k : Real) - 1 := by
    dsimp [m]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk.ne')]
    norm_num
  have hCount : 2 * (m : Real) + 2 * (1 : Real) = 2 * (k : Real) := by rw [hCast]; ring
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
  have hProfile := thresholdModel_all_selected d u m 1 hd (by decide) hu.1
  simp only [Nat.cast_one] at hProfile
  rw [hu.2, hCount] at hProfile
  have hTotal : Finset.sum Finset.univ (fun i => 2 * (thresholdPairWeights m 1 i : Real)) =
      2 * (k : Real) := by rw [thresholdPair_total]; simpa only [Nat.cast_one] using hCount
  have hBase : thresholdTotalAdmissible d M (2 * (k : Real)) (2 * (k : Real))
      (thresholdPairWeights m 1) (thresholdPairCoords u (thresholdModelHigh (m : Real) 1 u)) :=
    And.intro hTotal hProfile
  have hPad := thresholdTotalAdmissible_pad d M (2 * (k : Real)) (2 * (k : Real))
    (thresholdPairWeights m 1) (thresholdPairCoords u (thresholdModelHigh (m : Real) 1 u)) (n - k) hd.1 hBase
  have hN : 2 * ((n - k : Nat) : Real) + 2 * (k : Real) = 2 * (n : Real) := by
    rw [Nat.cast_sub hkn]
    ring
  rw [hN] at hPad
  exact Exists.intro _ (Exists.intro _ hPad)

theorem thresholdTotal_exists_upper (d M : Real) (n k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hkn : k <= n)
    (hLow : 2 * (k : Real) <= M)
    (hHigh : M < thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real))) :
    exists a : Fin 2 -> Nat, exists y : Fin 2 -> Real,
      thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y := by
  let m := n - k
  have hUpper : thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real)) =
      thresholdModelMass (m : Real) (k : Real) d := thresholdTotalUpper_even d n k hk hkn
  have hBetween : Membership.mem (Set.Icc (thresholdModelMass (m : Real) (k : Real) 0)
      (thresholdModelMass (m : Real) (k : Real) d)) M := by
    rw [thresholdModelMass_zero, <- hUpper]
    exact And.intro hLow hHigh.le
  choose u hu using intermediate_value_Icc hd.1.le
    (thresholdModelMass_continuous (m : Real) (k : Real)).continuousOn hBetween
  have huLt : u < d := by
    by_contra hn
    have huEq : u = d := le_antisymm hu.1.2 (le_of_not_gt hn)
    have hm := hu.2
    rw [huEq, <- hUpper] at hm
    linarith only [hm, hHigh]
  have huCut : And (0 <= u) (And (u < d) (u <= 1)) :=
    And.intro hu.1.1 (And.intro huLt (le_trans hu.1.2 hd.2.le))
  have hAd := thresholdModel_high_selected d u m k hd hk huCut
  rw [hu.2] at hAd
  have hTotal : Finset.sum Finset.univ (fun i => 2 * (thresholdPairWeights m k i : Real)) =
      2 * (n : Real) := by
    rw [thresholdPair_total]
    dsimp [m]
    rw [Nat.cast_sub hkn]
    ring
  exact Exists.intro _ (Exists.intro _ (And.intro hTotal hAd))

end PrimeFactorOscillations
