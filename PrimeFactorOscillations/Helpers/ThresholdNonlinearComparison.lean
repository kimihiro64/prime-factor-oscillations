/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DirectionalParityOptimality
import PrimeFactorOscillations.Helpers.ThresholdNonlinearCost

/-! # Explicit surviving gains beyond both sharp directional quadratics -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdPositiveBoundaryRatio (z : Real) : Real :=
  (1 - momentRoundThreshold) * z * (z ^ 2 - momentRoundThreshold ^ 2) /
    (z + 1 - momentRoundThreshold) ^ 2

def thresholdPositiveGainPolynomial (z : Real) : Real :=
  (1 - momentRoundThreshold) * z ^ 2 +
    (1 - momentRoundThreshold - positiveParityCoefficient) * z +
      positiveParityCoefficient * (1 - momentRoundThreshold) ^ 2

def thresholdNonlinearGain (M K : Real) : Real :=
  if K <= M then
    (thresholdPositiveBoundaryRatio (thresholdPositiveRoot momentRoundThreshold M K) -
      positiveParityCoefficient) * (M - K) ^ 2 / M
  else momentRoundThreshold ^ 3 * (K - M) ^ 3 /
    ((1 - momentRoundThreshold) * M * (M - momentRoundThreshold * K))

theorem positiveParityCoefficient_boundary_identity :
    positiveParityCoefficient * (2 - momentRoundThreshold) ^ 2 =
      (1 - momentRoundThreshold) * (1 - momentRoundThreshold ^ 2) := by
  have hDen : 0 < 2 - momentRoundThreshold := by
    have hd := momentRoundThreshold_bounds.2
    linarith only [hd]
  have hFrac := positiveParityRatio_zero
  unfold positiveParityRatio positiveParityHigh positiveParityLow positiveParityPolynomial at hFrac
  norm_num at hFrac
  change (1 - momentRoundThreshold) * (1 - momentRoundThreshold ^ 2) /
    (2 - momentRoundThreshold) ^ 2 = positiveParityCoefficient at hFrac
  have hScaled := congrArg (fun v : Real => v * (2 - momentRoundThreshold) ^ 2) hFrac
  have hCancel : ((1 - momentRoundThreshold) * (1 - momentRoundThreshold ^ 2) /
      (2 - momentRoundThreshold) ^ 2) * (2 - momentRoundThreshold) ^ 2 =
      (1 - momentRoundThreshold) * (1 - momentRoundThreshold ^ 2) := by field_simp [hDen.ne']
  nlinarith only [hScaled, hCancel]

theorem positiveParityCoefficient_lt_one_sub :
    positiveParityCoefficient < 1 - momentRoundThreshold := by
  have hd := momentRoundThreshold_bounds
  have hSquare := mul_pos (sub_pos.mpr hd.2)
    (show 0 < 1 / 2 + momentRoundThreshold by linarith only [hd.1])
  have hOne : 0 < 1 - 2 * momentRoundThreshold ^ 2 := by nlinarith only [hSquare]
  have hFactor := mul_pos (mul_pos (by norm_num : (0 : Real) < 2) hd.1) hOne
  unfold positiveParityCoefficient
  nlinarith only [hFactor]

theorem thresholdPositiveGainPolynomial_pos (z : Real) (hz : 1 <= z) :
    0 < thresholdPositiveGainPolynomial z := by
  have hOne : 0 < 1 - momentRoundThreshold := by
    have hd := momentRoundThreshold_bounds.2
    linarith only [hd]
  have hMiddle : 0 < 1 - momentRoundThreshold - positiveParityCoefficient :=
    sub_pos.mpr positiveParityCoefficient_lt_one_sub
  have hBeta := positiveParityCoefficient_pos
  have hzPos : 0 < z := by linarith only [hz]
  unfold thresholdPositiveGainPolynomial
  positivity

theorem thresholdPositiveBoundaryRatio_gain (z : Real) (hz : 1 <= z) :
    thresholdPositiveBoundaryRatio z - positiveParityCoefficient =
      (z - 1) * thresholdPositiveGainPolynomial z / (z + 1 - momentRoundThreshold) ^ 2 := by
  have hDen : 0 < z + 1 - momentRoundThreshold := by
    have hd := momentRoundThreshold_bounds.2
    linarith only [hz, hd]
  have hScaled := congrArg (fun v : Real => z * v) positiveParityCoefficient_boundary_identity
  have hPolynomial : (1 - momentRoundThreshold) * z * (z ^ 2 - momentRoundThreshold ^ 2) -
      positiveParityCoefficient * (z + 1 - momentRoundThreshold) ^ 2 =
      (z - 1) * thresholdPositiveGainPolynomial z := by
    unfold thresholdPositiveGainPolynomial
    nlinarith only [hScaled]
  unfold thresholdPositiveBoundaryRatio
  field_simp [hDen.ne']
  nlinarith only [hPolynomial]

theorem thresholdPositiveBoundaryRatio_ge (z : Real) (hz : 1 <= z) :
    positiveParityCoefficient <= thresholdPositiveBoundaryRatio z := by
  have hGain := thresholdPositiveBoundaryRatio_gain z hz
  have hNonneg : 0 <= (z - 1) * thresholdPositiveGainPolynomial z /
      (z + 1 - momentRoundThreshold) ^ 2 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hz) (thresholdPositiveGainPolynomial_pos z hz).le)
      (sq_nonneg _)
  linarith only [hGain, hNonneg]

theorem thresholdPositiveBoundaryRatio_gt (z : Real) (hz : 1 < z) :
    positiveParityCoefficient < thresholdPositiveBoundaryRatio z := by
  have hGain := thresholdPositiveBoundaryRatio_gain z hz.le
  have hDen : 0 < z + 1 - momentRoundThreshold := by
    have hd := momentRoundThreshold_bounds.2
    linarith only [hz, hd]
  have hPositive := div_pos (mul_pos (sub_pos.mpr hz) (thresholdPositiveGainPolynomial_pos z hz.le))
    (sq_pos_of_pos hDen)
  linarith only [hGain, hPositive]

theorem thresholdPositiveRoot_mass_formula (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hK : 0 < K) :
    M = K * thresholdPositiveRoot d M K * (thresholdPositiveRoot d M K - d) / (1 - d) := by
  have hOne : 0 < 1 - d := sub_pos.mpr hd.2
  have hRoot := thresholdPositiveRoot_relation d M K hd hM hK
  field_simp [hOne.ne']
  nlinarith only [hRoot]

theorem thresholdPositiveRoot_discrepancy_formula (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hK : 0 < K) :
    M - K = K * (thresholdPositiveRoot d M K - 1) *
      (thresholdPositiveRoot d M K + 1 - d) / (1 - d) := by
  let z := thresholdPositiveRoot d M K
  have hOne : 0 < 1 - d := sub_pos.mpr hd.2
  have hMass : M = K * z * (z - d) / (1 - d) := thresholdPositiveRoot_mass_formula d M K hd hM hK
  change M - K = K * (z - 1) * (z + 1 - d) / (1 - d)
  rw [hMass]
  field_simp [hOne.ne'] <;> ring

theorem thresholdPositiveCost_excess (M K : Real) (hM : 0 < M) (hK : 0 < K) :
    thresholdPositiveCost momentRoundThreshold M K - momentRoundThreshold * (M - K) =
      K * (thresholdPositiveRoot momentRoundThreshold M K - 1) ^ 2 *
        (thresholdPositiveRoot momentRoundThreshold M K + momentRoundThreshold) := by
  let d := momentRoundThreshold
  let z := thresholdPositiveRoot d M K
  have hd : And (0 < d) (d < 1) :=
    And.intro momentRoundThreshold_bounds.1 (by have hh := momentRoundThreshold_bounds.2; linarith)
  have hOne : 0 < 1 - d := sub_pos.mpr hd.2
  have hMass : M = K * z * (z - d) / (1 - d) := thresholdPositiveRoot_mass_formula d M K hd hM hK
  have hScaled := congrArg (fun v : Real => z * v) momentRoundThreshold_equation
  have hPolynomial : z * (z - d) * (1 - d) - d * (z + 1 - d) =
      (z - 1) * (1 - d) * (z + d) := by
    change z * (z - momentRoundThreshold) * (1 - momentRoundThreshold) -
      momentRoundThreshold * (z + 1 - momentRoundThreshold) =
      (z - 1) * (1 - momentRoundThreshold) * (z + momentRoundThreshold)
    nlinarith only [hScaled]
  change M * (1 - d) * (z - 1) - d * (M - K) = K * (z - 1) ^ 2 * (z + d)
  calc
    _ = K * (z - 1) / (1 - d) *
        (z * (z - d) * (1 - d) - d * (z + 1 - d)) := by
      rw [hMass]
      field_simp [hOne.ne'] <;> ring
    _ = _ := by rw [hPolynomial]; field_simp [hOne.ne'] <;> ring

theorem thresholdPositiveCost_exact_ratio (M K : Real)
    (hM : 0 < M) (hK : 0 < K) (hKM : K <= M) :
    M * (thresholdPositiveCost momentRoundThreshold M K - momentRoundThreshold * (M - K)) =
      thresholdPositiveBoundaryRatio (thresholdPositiveRoot momentRoundThreshold M K) * (M - K) ^ 2 := by
  let d := momentRoundThreshold
  let z := thresholdPositiveRoot d M K
  have hd : And (0 < d) (d < 1) :=
    And.intro momentRoundThreshold_bounds.1 (by have hh := momentRoundThreshold_bounds.2; linarith)
  have hOne : 0 < 1 - d := sub_pos.mpr hd.2
  have hz := (thresholdPositiveRoot_bounds d M K hd hM hK hKM).2
  have hDen : 0 < z + 1 - d := by linarith only [hz, hd.2]
  have hMass : M = K * z * (z - d) / (1 - d) := thresholdPositiveRoot_mass_formula d M K hd hM hK
  have hD : M - K = K * (z - 1) * (z + 1 - d) / (1 - d) :=
    thresholdPositiveRoot_discrepancy_formula d M K hd hM hK
  rw [thresholdPositiveCost_excess M K hM hK]
  change M * (K * (z - 1) ^ 2 * (z + d)) = thresholdPositiveBoundaryRatio z * (M - K) ^ 2
  rw [hD, hMass]
  unfold thresholdPositiveBoundaryRatio
  change (K * z * (z - d) / (1 - d)) * (K * (z - 1) ^ 2 * (z + d)) =
    ((1 - d) * z * (z ^ 2 - d ^ 2) / (z + 1 - d) ^ 2) *
      (K * (z - 1) * (z + 1 - d) / (1 - d)) ^ 2
  field_simp [hOne.ne', hDen.ne'] <;> ring

theorem thresholdPositiveCost_gain (M K : Real)
    (hM : 0 < M) (hK : 0 < K) (hKM : K <= M) :
    thresholdPositiveCost momentRoundThreshold M K = momentRoundThreshold * (M - K) +
      positiveParityCoefficient * (M - K) ^ 2 / M +
        (thresholdPositiveBoundaryRatio (thresholdPositiveRoot momentRoundThreshold M K) -
          positiveParityCoefficient) * (M - K) ^ 2 / M := by
  have hRatio := thresholdPositiveCost_exact_ratio M K hM hK hKM
  field_simp [hM.ne']
  nlinarith only [hRatio]

theorem sharpParityCoefficient_quotient :
    sharpParityCoefficient = momentRoundThreshold ^ 2 / (1 - momentRoundThreshold) := by
  have hOne : 0 < 1 - momentRoundThreshold := by
    have hd := momentRoundThreshold_bounds.2
    linarith only [hd]
  field_simp [hOne.ne']
  unfold sharpParityCoefficient
  nlinarith only [momentRoundThreshold_equation]

theorem thresholdNegativeCost_gain (M K : Real)
    (hM : 0 < M) (hDomain : momentRoundThreshold * K < M) :
    thresholdNegativeCost momentRoundThreshold M K = momentRoundThreshold * (K - M) +
      sharpParityCoefficient * (K - M) ^ 2 / M +
        momentRoundThreshold ^ 3 * (K - M) ^ 3 /
          ((1 - momentRoundThreshold) * M * (M - momentRoundThreshold * K)) := by
  have hOne : 0 < 1 - momentRoundThreshold := by
    have hd := momentRoundThreshold_bounds.2
    linarith only [hd]
  have hDen : 0 < M - momentRoundThreshold * K := sub_pos.mpr hDomain
  rw [sharpParityCoefficient_quotient]
  unfold thresholdNegativeCost
  field_simp [hOne.ne', hM.ne', hDen.ne'] <;> ring

theorem thresholdNonlinearGain_identity (M K : Real)
    (hM : 0 < M) (hK : 0 < K) (hDomain : momentRoundThreshold * K < M) :
    thresholdNonlinearCost momentRoundThreshold M K =
      directionalParityStabilityCost M (M - K) + thresholdNonlinearGain M K := by
  unfold thresholdNonlinearCost thresholdNonlinearGain
  by_cases hSide : K <= M
  case pos =>
    simp only [if_pos hSide]
    have hD : 0 <= M - K := sub_nonneg.mpr hSide
    rw [directionalParityStabilityCost, if_pos hD, abs_of_nonneg hD]
    exact thresholdPositiveCost_gain M K hM hK hSide
  case neg =>
    simp only [if_neg hSide]
    have hD : M - K < 0 := sub_neg.mpr (lt_of_not_ge hSide)
    have hAbs : abs (M - K) = K - M := by rw [abs_of_neg hD]; ring
    have hSq : (M - K) ^ 2 = (K - M) ^ 2 := by ring
    rw [directionalParityStabilityCost, if_neg (not_le.mpr hD), hAbs, hSq]
    exact thresholdNegativeCost_gain M K hM hDomain

theorem thresholdNonlinearGain_pos (M K : Real)
    (hM : 0 < M) (hK : 0 < K) (hDomain : momentRoundThreshold * K < M) (hDifferent : Not (K = M)) :
    0 < thresholdNonlinearGain M K := by
  unfold thresholdNonlinearGain
  by_cases hSide : K <= M
  case pos =>
    rw [if_pos hSide]
    have hKM : K < M := by
      by_contra hn
      exact hDifferent (le_antisymm hSide (le_of_not_gt hn))
    have hd : And (0 < momentRoundThreshold) (momentRoundThreshold < 1) :=
      And.intro momentRoundThreshold_bounds.1 (by have hh := momentRoundThreshold_bounds.2; linarith)
    have hz := thresholdPositiveRoot_gt_one momentRoundThreshold M K hd hM hK hKM
    have hRatio := sub_pos.mpr (thresholdPositiveBoundaryRatio_gt _ hz)
    exact div_pos (mul_pos hRatio (sq_pos_of_pos (sub_pos.mpr hKM))) hM
  case neg =>
    rw [if_neg hSide]
    have hU : 0 < K - M := sub_pos.mpr (lt_of_not_ge hSide)
    have hd := momentRoundThreshold_bounds
    have hOne : 0 < 1 - momentRoundThreshold := by linarith only [hd.2]
    have hDen : 0 < M - momentRoundThreshold * K := sub_pos.mpr hDomain
    exact div_pos (mul_pos (pow_pos hd.1 3) (pow_pos hU 3))
      (mul_pos (mul_pos hOne hM) hDen)

theorem thresholdNonlinearGain_nonneg (M K : Real)
    (hM : 0 < M) (hK : 0 < K) (hDomain : momentRoundThreshold * K < M) :
    0 <= thresholdNonlinearGain M K := by
  by_cases hEq : K = M
  case pos => simp [hEq, thresholdNonlinearGain]
  case neg => exact (thresholdNonlinearGain_pos M K hM hK hDomain hEq).le

theorem thresholdNonlinearCost_dominates (M K : Real)
    (hM : 0 < M) (hK : 0 < K) (hDomain : momentRoundThreshold * K < M) :
    directionalParityStabilityCost M (M - K) <= thresholdNonlinearCost momentRoundThreshold M K := by
  rw [thresholdNonlinearGain_identity M K hM hK hDomain]
  exact le_add_of_nonneg_right (thresholdNonlinearGain_nonneg M K hM hK hDomain)

theorem thresholdNonlinearCost_strict (M K : Real)
    (hM : 0 < M) (hK : 0 < K) (hDomain : momentRoundThreshold * K < M) (hDifferent : Not (K = M)) :
    directionalParityStabilityCost M (M - K) < thresholdNonlinearCost momentRoundThreshold M K := by
  rw [thresholdNonlinearGain_identity M K hM hK hDomain]
  exact lt_add_of_pos_right _ (thresholdNonlinearGain_pos M K hM hK hDomain hDifferent)

end PrimeFactorOscillations
