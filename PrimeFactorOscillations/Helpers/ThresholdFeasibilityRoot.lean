/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdFeasibilityEnvelope

/-! # The admissible root and sharp inverse selected-order boundary -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdMinimumMass (d K : Real) : Real :=
  d * (K - 2) + 1 + Real.sqrt (1 + 2 * (K - 2) * d * (1 - d))

def thresholdMaxSelected (d M : Real) : Real :=
  (M + d - Real.sqrt (d ^ 2 + 2 * (1 - d) * M)) / d

theorem thresholdMinimumMass_radical (d K : Real)
    (hd : And (0 < d) (d < 1)) (hK : 2 <= K) :
    And (0 <= 1 + 2 * (K - 2) * d * (1 - d))
      (1 <= Real.sqrt (1 + 2 * (K - 2) * d * (1 - d))) := by
  have hP := mul_nonneg (mul_nonneg (sub_nonneg.mpr hK) hd.1.le)
    (sub_nonneg.mpr hd.2.le)
  have hD : 0 <= 1 + 2 * (K - 2) * d * (1 - d) := by nlinarith only [hP]
  have hS := Real.sqrt_nonneg (1 + 2 * (K - 2) * d * (1 - d))
  have hSq := Real.sq_sqrt hD
  exact And.intro hD (by nlinarith only [hP, hS, hSq])

theorem thresholdMinimumMass_bounds (d K : Real)
    (hd : And (0 < d) (d < 1)) (hK : 2 <= K) :
    And (2 <= thresholdMinimumMass d K)
      (And (d * K < thresholdMinimumMass d K) (thresholdMinimumMass d K <= K)) := by
  have hR := thresholdMinimumMass_radical d K hd hK
  have hTerm := mul_nonneg hd.1.le (sub_nonneg.mpr hK)
  have hLow : 2 <= thresholdMinimumMass d K := by
    unfold thresholdMinimumMass
    linarith only [hR.2, hTerm]
  have hGap : d * K < thresholdMinimumMass d K := by
    unfold thresholdMinimumMass
    nlinarith only [hR.2, hd.2]
  let B := 1 + (K - 2) * (1 - d)
  have hB : 0 <= B := by
    have hp := mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hd.2.le)
    dsimp [B]
    linarith only [hp]
  have hSquare : (1 + 2 * (K - 2) * d * (1 - d)) <= B ^ 2 := by
    have hp := mul_nonneg (mul_nonneg (sub_nonneg.mpr hK) (by linarith only [hK] : 0 <= K))
      (sq_nonneg (1 - d))
    have hh : B ^ 2 - (1 + 2 * (K - 2) * d * (1 - d)) =
        (K - 2) * K * (1 - d) ^ 2 := by dsimp [B]; ring
    linarith only [hp, hh]
  have hS := Real.sqrt_nonneg (1 + 2 * (K - 2) * d * (1 - d))
  have hSq := Real.sq_sqrt hR.1
  have hSB : Real.sqrt (1 + 2 * (K - 2) * d * (1 - d)) <= B := by
    nlinarith only [hS, hSq, hSquare, hB]
  have hUpper : thresholdMinimumMass d K <= K := by
    dsimp [B] at hSB
    unfold thresholdMinimumMass
    nlinarith only [hSB]
  exact And.intro hLow (And.intro hGap hUpper)

theorem thresholdMinimumMass_quadratic (d K : Real)
    (hd : And (0 < d) (d < 1)) (hK : 2 <= K) :
    (thresholdMinimumMass d K - d * K) ^ 2 +
      (4 * d - 2) * thresholdMinimumMass d K - 2 * d ^ 2 * K = 0 := by
  have hD := (thresholdMinimumMass_radical d K hd hK).1
  have hSq := Real.sq_sqrt hD
  calc
    _ = (Real.sqrt (1 + 2 * (K - 2) * d * (1 - d))) ^ 2 -
        (1 + 2 * (K - 2) * d * (1 - d)) := by unfold thresholdMinimumMass; ring
    _ = 0 := by rw [hSq]; ring

theorem thresholdQuadratic_mass_floor (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hK : 2 <= K) (hMK : d * K < M)
    (hP : (M - d * K) ^ 2 + (4 * d - 2) * M - 2 * d ^ 2 * K >= 0) :
    thresholdMinimumMass d K <= M := by
  let R := thresholdMinimumMass d K
  have hRoot := thresholdMinimumMass_quadratic d K hd hK
  have hR := (thresholdMinimumMass_radical d K hd hK).2
  have hFactor :
      (M - d * K) ^ 2 + (4 * d - 2) * M - 2 * d ^ 2 * K -
      ((R - d * K) ^ 2 + (4 * d - 2) * R - 2 * d ^ 2 * K) =
      (M - R) * (M + R - 2 * (d * (K - 2) + 1)) := by ring
  have hPositive : 0 < M + R - 2 * (d * (K - 2) + 1) := by
    dsimp [R, thresholdMinimumMass]
    nlinarith only [hMK, hR, hd.1]
  by_contra hn
  have hNeg : M - R < 0 := sub_neg.mpr (lt_of_not_ge hn)
  have hProduct := mul_neg_of_neg_of_pos hNeg hPositive
  change (R - d * K) ^ 2 + (4 * d - 2) * R - 2 * d ^ 2 * K = 0 at hRoot
  linarith only [hP, hRoot, hFactor, hProduct]

theorem thresholdQuadratic_inverse_count (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hMK : d * K < M)
    (hP : (M - d * K) ^ 2 + (4 * d - 2) * M - 2 * d ^ 2 * K >= 0) :
    K <= thresholdMaxSelected d M := by
  let B := M + d - d * K
  let E := d ^ 2 + 2 * (1 - d) * M
  have hB : 0 < B := by dsimp [B]; linarith only [hMK, hd.1]
  have hE : 0 <= E := by
    have hp := mul_nonneg (sub_nonneg.mpr hd.2.le) hM.le
    dsimp [E]
    nlinarith only [hp, sq_nonneg d]
  have hBSquare : E <= B ^ 2 := by dsimp [E, B]; nlinarith only [hP]
  have hS := Real.sqrt_nonneg E
  have hSq := Real.sq_sqrt hE
  have hSB : Real.sqrt E <= B := by nlinarith only [hB, hBSquare, hS, hSq]
  have hIdentity : d * thresholdMaxSelected d M = M + d - Real.sqrt E := by
    unfold thresholdMaxSelected
    dsimp [E]
    field_simp [hd.1.ne']
  have hScaled : d * K <= d * thresholdMaxSelected d M := by
    dsimp [B] at hSB
    linarith only [hSB, hIdentity]
  nlinarith only [hScaled, hd.1]

theorem thresholdEvenAdmissible_domain {n : Nat} (d M K : Real)
    (a : Fin n -> Nat) (y : Fin n -> Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K)
    (hAd : thresholdEvenAdmissible d M K a y) : And (0 < M) (d * K < M) := by
  have ha := fun (i : Fin n) (_ : Membership.mem Finset.univ i) =>
    mul_nonneg (show (0 : Real) <= 2 by norm_num) (Nat.cast_nonneg (a i))
  have hX := Finset.sum_nonneg (fun (i : Fin n) (_ : Membership.mem Finset.univ i) =>
    mul_nonneg (ha i (Finset.mem_univ i)) (thresholdExcess_nonneg d (y i)))
  have hY := Finset.sum_nonneg (fun (i : Fin n) (_ : Membership.mem Finset.univ i) =>
    mul_nonneg (ha i (Finset.mem_univ i)) (thresholdLow_nonneg d (y i) (hAd.1 i)))
  have hLedger := (finiteWeighted_threshold_ledger Finset.univ (fun i => 2 * (a i : Real)) y d).1
  rw [hAd.2.1, hAd.2.2.2] at hLedger
  have hM : 0 < M := by linarith only [hLedger, hX, hY, mul_pos hd.1 hK]
  have hDom := finiteWeightedThreshold_domain Finset.univ (fun i => 2 * (a i : Real)) y d hd.2
    ha (fun i _ => hAd.1 i) (by rw [hAd.2.2.1, hAd.2.1]) (by rw [hAd.2.1]; exact hM)
  rw [hAd.2.1, hAd.2.2.2] at hDom
  exact And.intro hM hDom.2

theorem thresholdEvenAdmissible_mass_floor {n : Nat} (d M K : Real)
    (a : Fin n -> Nat) (y : Fin n -> Real)
    (hd : And (0 < d) (d < 1)) (hK : 2 <= K)
    (hAd : thresholdEvenAdmissible d M K a y) : thresholdMinimumMass d K <= M := by
  have hDom := thresholdEvenAdmissible_domain d M K a y hd (by linarith only [hK]) hAd
  exact thresholdQuadratic_mass_floor d M K hd hK hDom.2
    (thresholdEvenAdmissible_quadratic d M K a y hd.1.le hAd)

theorem thresholdEvenAdmissible_inverse_count {n : Nat} (d M K : Real)
    (a : Fin n -> Nat) (y : Fin n -> Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K)
    (hAd : thresholdEvenAdmissible d M K a y) : K <= thresholdMaxSelected d M := by
  have hDom := thresholdEvenAdmissible_domain d M K a y hd hK hAd
  exact thresholdQuadratic_inverse_count d M K hd hDom.1 hDom.2
    (thresholdEvenAdmissible_quadratic d M K a y hd.1.le hAd)

end PrimeFactorOscillations
