/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DirectionalParityStability

/-! # Optimal directional compensated parity coefficients -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations


def positiveParityLow (e : Real) : Real := momentRoundThreshold - e ^ 2

def positiveParityHigh (e : Real) : Real := 1 + e

def positiveParityWeight (e : Real) : Real :=
  positiveParityHigh e * (positiveParityHigh e - 1) /
    (positiveParityLow e * (1 - positiveParityLow e))

def positiveParityMass (e : Real) : Real :=
  positiveParityWeight e * positiveParityLow e + positiveParityHigh e

def positiveParityDiscrepancy (e : Real) : Real := positiveParityMass e - 1

def positiveParityEnergy (e : Real) : Real :=
  positiveParityWeight e * positiveParityLow e * (positiveParityLow e - 1) ^ 2 +
    positiveParityHigh e * (positiveParityHigh e - 1) ^ 2

def positiveParityPolynomial (e : Real) : Real :=
  1 - momentRoundThreshold ^ 2 + (3 - 4 * momentRoundThreshold) * e +
    (3 - 2 * momentRoundThreshold) * e ^ 2 + 2 * e ^ 3 + e ^ 4

def positiveParityRatio (e : Real) : Real :=
  positiveParityHigh e * (positiveParityHigh e - positiveParityLow e) *
    positiveParityPolynomial e / (positiveParityHigh e + 1 - positiveParityLow e) ^ 2

theorem positiveParityLow_bounds (e : Real) (he : And (0 < e) (e < 1 / 2)) :
    And (0 < positiveParityLow e) (positiveParityLow e < momentRoundThreshold) := by
  unfold positiveParityLow
  have hMul := mul_pos (sub_pos.mpr he.2) (show 0 < 1 / 2 + e by linarith)
  have hD := momentRoundThreshold_gt_quarter
  have hSq := sq_pos_of_pos he.1
  constructor <;> nlinarith only [hMul, hD, hSq]

theorem positiveParityHigh_gt_one (e : Real) (he : 0 < e) :
    1 < positiveParityHigh e := by unfold positiveParityHigh; linarith

theorem positiveParityWeight_pos (e : Real) (he : And (0 < e) (e < 1 / 2)) :
    0 < positiveParityWeight e := by
  have hU := positiveParityLow_bounds e he
  have hD := momentRoundThreshold_bounds.2
  have hZ := positiveParityHigh_gt_one e he.1
  unfold positiveParityWeight
  exact div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hU.1 (by linarith))

theorem positiveParityMass_formula (e : Real) (he : And (0 < e) (e < 1 / 2)) :
    positiveParityMass e = positiveParityHigh e * (positiveParityHigh e - positiveParityLow e) /
      (1 - positiveParityLow e) := by
  have hU := positiveParityLow_bounds e he
  have hD := momentRoundThreshold_bounds.2
  have hOne : 0 < 1 - positiveParityLow e := by linarith
  unfold positiveParityMass positiveParityWeight
  field_simp [hU.1.ne', hOne.ne']
  ring

theorem positiveParityDiscrepancy_formula (e : Real) (he : And (0 < e) (e < 1 / 2)) :
    positiveParityDiscrepancy e =
      e * (positiveParityHigh e + 1 - positiveParityLow e) / (1 - positiveParityLow e) := by
  have hU := positiveParityLow_bounds e he
  have hD := momentRoundThreshold_bounds.2
  have hOne : 0 < 1 - positiveParityLow e := by linarith
  unfold positiveParityDiscrepancy
  rw [positiveParityMass_formula e he]
  unfold positiveParityHigh
  field_simp [hOne.ne']
  ring

theorem positiveParityEnergy_formula (e : Real) (he : And (0 < e) (e < 1 / 2)) :
    positiveParityEnergy e =
      positiveParityHigh e * e * (positiveParityHigh e - positiveParityLow e) := by
  have hU := positiveParityLow_bounds e he
  have hD := momentRoundThreshold_bounds.2
  have hOne : 0 < 1 - positiveParityLow e := by linarith
  unfold positiveParityEnergy positiveParityWeight
  field_simp [hU.1.ne', hOne.ne']
  unfold positiveParityHigh
  ring

theorem positiveParity_moment (e : Real) (he : And (0 < e) (e < 1 / 2)) :
    positiveParityWeight e * positiveParityLow e ^ 2 + positiveParityHigh e ^ 2 =
      positiveParityMass e := by
  have hU := positiveParityLow_bounds e he
  have hD := momentRoundThreshold_bounds.2
  have hOne : 0 < 1 - positiveParityLow e := by linarith
  unfold positiveParityMass positiveParityWeight
  field_simp [hU.1.ne', hOne.ne']
  ring

theorem positiveParityMass_pos (e : Real) (he : And (0 < e) (e < 1 / 2)) :
    0 < positiveParityMass e := by
  unfold positiveParityMass
  exact add_pos (mul_pos (positiveParityWeight_pos e he) (positiveParityLow_bounds e he).1)
    (lt_trans (by norm_num) (positiveParityHigh_gt_one e he.1))

theorem positiveParityDiscrepancy_pos (e : Real) (he : And (0 < e) (e < 1 / 2)) :
    0 < positiveParityDiscrepancy e := by
  have hU := positiveParityLow_bounds e he
  have hD := momentRoundThreshold_bounds.2
  have hZ := positiveParityHigh_gt_one e he.1
  rw [positiveParityDiscrepancy_formula e he]
  exact div_pos (mul_pos he.1 (by linarith)) (by linarith)

theorem positiveParity_excess_polynomial (e : Real) :
    positiveParityHigh e * (positiveParityHigh e - positiveParityLow e) * (1 - positiveParityLow e) -
      momentRoundThreshold * (positiveParityHigh e + 1 - positiveParityLow e) =
      e * positiveParityPolynomial e := by
  calc
    _ = e * positiveParityPolynomial e + (1 + e) *
        (2 * momentRoundThreshold ^ 2 - 4 * momentRoundThreshold + 1) := by
      unfold positiveParityHigh positiveParityLow positiveParityPolynomial
      ring
    _ = _ := by rw [momentRoundThreshold_equation]; ring

theorem positiveParityEnergy_excess (e : Real) (he : And (0 < e) (e < 1 / 2)) :
    positiveParityEnergy e - momentRoundThreshold * positiveParityDiscrepancy e =
      e ^ 2 * positiveParityPolynomial e / (1 - positiveParityLow e) := by
  have hU := positiveParityLow_bounds e he
  have hD := momentRoundThreshold_bounds.2
  have hOne : 0 < 1 - positiveParityLow e := by linarith
  calc
    _ = e * (positiveParityHigh e * (positiveParityHigh e - positiveParityLow e) *
          (1 - positiveParityLow e) -
          momentRoundThreshold * (positiveParityHigh e + 1 - positiveParityLow e)) /
          (1 - positiveParityLow e) := by
      rw [positiveParityEnergy_formula e he, positiveParityDiscrepancy_formula e he]
      field_simp [hOne.ne'] <;> ring
    _ = _ := by rw [positiveParity_excess_polynomial]; ring

theorem positiveParity_exact_ratio (e : Real) (he : And (0 < e) (e < 1 / 2)) :
    positiveParityMass e *
      (positiveParityEnergy e - momentRoundThreshold * positiveParityDiscrepancy e) =
      positiveParityRatio e * positiveParityDiscrepancy e ^ 2 := by
  have hU := positiveParityLow_bounds e he
  have hD := momentRoundThreshold_bounds.2
  have hZ := positiveParityHigh_gt_one e he.1
  have hOne : 0 < 1 - positiveParityLow e := by linarith
  have hHigh : 0 < positiveParityHigh e + 1 - positiveParityLow e := by linarith
  rw [positiveParityMass_formula e he, positiveParityEnergy_excess e he,
    positiveParityDiscrepancy_formula e he]
  unfold positiveParityRatio
  field_simp [hOne.ne', hHigh.ne'] <;> ring

theorem positiveParityRatio_zero : positiveParityRatio 0 = positiveParityCoefficient := by
  have hD := momentRoundThreshold_bounds.2
  have hDen : 0 < 2 - momentRoundThreshold := by linarith
  have hRel : 1 - momentRoundThreshold =
      (1 - 2 * momentRoundThreshold) * (2 - momentRoundThreshold) := by
    nlinarith only [momentRoundThreshold_equation]
  have hNum : (1 - momentRoundThreshold) * (1 - momentRoundThreshold ^ 2) =
      positiveParityCoefficient * (2 - momentRoundThreshold) ^ 2 := by
    calc
      _ = (1 + momentRoundThreshold) * (1 - momentRoundThreshold) ^ 2 := by ring
      _ = (1 + momentRoundThreshold) *
          ((1 - 2 * momentRoundThreshold) * (2 - momentRoundThreshold)) ^ 2 := by rw [hRel]
      _ = _ := by unfold positiveParityCoefficient; ring
  unfold positiveParityRatio positiveParityHigh positiveParityLow positiveParityPolynomial
  norm_num
  change (1 - momentRoundThreshold) * (1 - momentRoundThreshold ^ 2) /
    (2 - momentRoundThreshold) ^ 2 = positiveParityCoefficient
  rw [hNum]
  field_simp [hDen.ne']

theorem positiveParityRatio_continuousAt_zero : ContinuousAt positiveParityRatio 0 := by
  have hD := momentRoundThreshold_bounds.2
  have hDen : Not (2 - momentRoundThreshold = 0) := ne_of_gt (by linarith)
  unfold positiveParityRatio positiveParityHigh positiveParityLow positiveParityPolynomial
  fun_prop (disch := norm_num [hDen])

theorem positiveParity_counterexample (c : Real) (hc : positiveParityCoefficient < c) :
    exists e : Real, And (And (0 < e) (e < 1 / 2))
      (positiveParityEnergy e < momentRoundThreshold * positiveParityDiscrepancy e +
        c * positiveParityDiscrepancy e ^ 2 / positiveParityMass e) := by
  choose radius hRadius hClose using
    (Metric.continuousAt_iff.mp positiveParityRatio_continuousAt_zero)
      (c - positiveParityCoefficient) (sub_pos.mpr hc)
  let e := min (radius / 2) (1 / 4)
  have he0 : 0 < e := lt_min (by linarith) (by norm_num)
  have heHalf : e < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heRadius : e < radius := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hDist : dist e 0 < radius := by
    rw [Real.dist_eq, sub_zero, abs_of_pos he0]
    exact heRadius
  have hNear := hClose hDist
  rw [positiveParityRatio_zero, Real.dist_eq] at hNear
  have hRlt : positiveParityRatio e < c := by
    have hh := (abs_lt.mp hNear).2
    linarith only [hh]
  have he : And (0 < e) (e < 1 / 2) := And.intro he0 heHalf
  have hM := positiveParityMass_pos e he
  have hD := positiveParityDiscrepancy_pos e he
  have hRatio := positiveParity_exact_ratio e he
  have hStrict := mul_pos (sub_pos.mpr hRlt) (sq_pos_of_pos hD)
  have hCancel : (c * positiveParityDiscrepancy e ^ 2 / positiveParityMass e) *
      positiveParityMass e = c * positiveParityDiscrepancy e ^ 2 := by field_simp [hM.ne']
  refine Exists.intro e (And.intro he ?_)
  by_contra hn
  have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) hM.le
  nlinarith only [hRatio, hStrict, hCancel, hp]


def DirectionalParityCoefficientAdmissible (cp cm : Real) : Prop :=
  forall (m : Nat) (a y : Fin m -> Real),
    (forall i, 0 <= a i) ->
    (forall i, 0 <= y i) ->
    let M := Finset.sum Finset.univ (fun i => a i * y i)
    let D := M - Finset.sum Finset.univ
      (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))
    let E := Finset.sum Finset.univ (fun i => a i * y i * (y i - 1) ^ 2)
    (Finset.sum Finset.univ (fun i => a i * (y i) ^ 2) = M) ->
    0 < M ->
    momentRoundThreshold * abs D + (if 0 <= D then cp else cm) * D ^ 2 / M <= E

theorem directionalParityCoefficientAdmissible_iff (cp cm : Real) :
    DirectionalParityCoefficientAdmissible cp cm <->
      And (cp <= positiveParityCoefficient) (cm <= sharpParityCoefficient) := by
  constructor
  case mp =>
    intro hValid
    constructor
    case left =>
      by_contra hn
      have hc : positiveParityCoefficient < cp := lt_of_not_ge hn
      choose e he using positiveParity_counterexample cp hc
      let a : Fin 2 -> Real := fun i => if i = 0 then positiveParityWeight e else 1
      let y : Fin 2 -> Real := fun i => if i = 0 then positiveParityLow e else positiveParityHigh e
      have hU := positiveParityLow_bounds e he.1
      have hZ := positiveParityHigh_gt_one e he.1.1
      have ha : forall i, 0 <= a i := by
        intro i
        dsimp only [a]
        by_cases hi : i = 0
        case pos => rw [if_pos hi]; exact (positiveParityWeight_pos e he.1).le
        case neg => rw [if_neg hi]; norm_num
      have hy : forall i, 0 <= y i := by
        intro i
        dsimp only [y]
        by_cases hi : i = 0
        case pos => rw [if_pos hi]; exact hU.1.le
        case neg => rw [if_neg hi]; linarith
      have hMoment : Finset.sum Finset.univ (fun i => a i * (y i) ^ 2) =
          Finset.sum Finset.univ (fun i => a i * y i) := by
        simpa [Fin.sum_univ_two, a, y, positiveParityMass] using positiveParity_moment e he.1
      have hMass : 0 < Finset.sum Finset.univ (fun i => a i * y i) := by
        simpa [Fin.sum_univ_two, a, y, positiveParityMass] using positiveParityMass_pos e he.1
      have hBound := hValid 2 a y ha hy hMoment hMass
      have hLow : Not (momentRoundThreshold <= positiveParityLow e) := not_le_of_gt hU.2
      have hHigh : momentRoundThreshold <= positiveParityHigh e := by
        have hd := momentRoundThreshold_bounds.2
        linarith
      have hD : 0 < positiveParityWeight e * positiveParityLow e + positiveParityHigh e - 1 :=
        positiveParityDiscrepancy_pos e he.1
      have hModel : momentRoundThreshold * positiveParityDiscrepancy e +
          cp * positiveParityDiscrepancy e ^ 2 / positiveParityMass e <= positiveParityEnergy e := by
        simpa [Fin.sum_univ_two, a, y, positiveParityMass, positiveParityDiscrepancy,
          positiveParityEnergy, momentRoundIndicator, hLow, hHigh, hD.le, abs_of_pos hD] using hBound
      linarith only [hModel, he.2]
    case right =>
      by_contra hn
      have hc : sharpParityCoefficient < cm := lt_of_not_ge hn
      choose n hn using evenParityPair_counterexample cm hc
      let a : Fin 2 -> Real := fun i => (evenParityWeights n i : Real)
      let y : Fin 2 -> Real := evenParityCoordinates n
      have ha : forall i, 0 <= a i := fun i => Nat.cast_nonneg _
      have hy : forall i, 0 <= y i := evenParityCoordinates_nonneg n hn.1
      have hMoment : Finset.sum Finset.univ (fun i => a i * (y i) ^ 2) =
          Finset.sum Finset.univ (fun i => a i * y i) := by
        simpa [Fin.sum_univ_two, a, y, evenParityWeights, evenParityCoordinates,
          evenParityPairMass, Nat.cast_mul] using evenParityPair_moment n hn.1
      have hMass : 0 < Finset.sum Finset.univ (fun i => a i * y i) := by
        simpa [Fin.sum_univ_two, a, y, evenParityWeights, evenParityCoordinates,
          evenParityPairMass, Nat.cast_mul] using evenParityPair_mass_pos n hn.1
      have hBound := hValid 2 a y ha hy hMoment hMass
      have hHigh : momentRoundThreshold <= evenParityCoordinate n := by
        have hd := momentRoundThreshold_bounds.2
        have hz := evenParityCoordinate_gt_one n hn.1
        linarith
      have hD : 2 * momentRoundThreshold + (2 * (n : Real)) * evenParityCoordinate n -
          (2 + 2 * (n : Real)) < 0 := evenParityPair_discrepancy_neg n hn.1
      have hDNot : Not (0 <= 2 * momentRoundThreshold + (2 * (n : Real)) * evenParityCoordinate n -
          (2 + 2 * (n : Real))) := not_le_of_gt hD
      have hModel : momentRoundThreshold * abs (evenParityPairDiscrepancy n) +
          cm * evenParityPairDiscrepancy n ^ 2 / evenParityPairMass n <= evenParityPairEnergy n := by
        simpa [Fin.sum_univ_two, a, y, evenParityWeights, evenParityCoordinates,
          evenParityPairMass, evenParityPairDiscrepancy, evenParityPairEnergy,
          momentRoundIndicator, hHigh, Nat.cast_mul, hDNot] using hBound
      linarith only [hModel, hn.2]
  case mpr =>
    intro hCoeffs
    intro m a y ha hy
    dsimp only
    intro hMoment hMass
    let M := Finset.sum Finset.univ (fun i => a i * y i)
    let D := M - Finset.sum Finset.univ
      (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))
    let E := Finset.sum Finset.univ (fun i => a i * y i * (y i - 1) ^ 2)
    have hSharp := finiteWeightedParity_directional_stability Finset.univ a y
      (fun i _ => ha i) (fun i _ => hy i) hMoment hMass
    change directionalParityStabilityCost M D <= E at hSharp
    change momentRoundThreshold * abs D + (if 0 <= D then cp else cm) * D ^ 2 / M <= E
    unfold directionalParityStabilityCost at hSharp
    have hC : (if 0 <= D then cp else cm) <=
        (if 0 <= D then positiveParityCoefficient else sharpParityCoefficient) := by
      by_cases hD : 0 <= D
      case pos => simpa only [if_pos hD] using hCoeffs.1
      case neg => simpa only [if_neg hD] using hCoeffs.2
    have hRatio : 0 <= D ^ 2 / M := div_nonneg (sq_nonneg D) hMass.le
    have hGain := mul_nonneg (sub_nonneg.mpr hC) hRatio
    have hAlgebra :
        ((if 0 <= D then positiveParityCoefficient else sharpParityCoefficient) -
          (if 0 <= D then cp else cm)) * (D ^ 2 / M) =
        (if 0 <= D then positiveParityCoefficient else sharpParityCoefficient) * D ^ 2 / M -
          (if 0 <= D then cp else cm) * D ^ 2 / M := by ring
    rw [hAlgebra] at hGain
    linarith only [hSharp, hGain]

end PrimeFactorOscillations
