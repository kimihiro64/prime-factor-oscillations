/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.SharpCompensatedParityStability

/-! # Optimal sharp parity stability for even integral weights

The counterexamples are finite moment profiles, not actual zeta zero sets.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations


def evenParityCoordinate (n : Nat) : Real :=
  (1 + Real.sqrt (1 + 2 * (1 - 2 * momentRoundThreshold) / (n : Real))) / 2

def evenParityPairMass (n : Nat) : Real :=
  2 * momentRoundThreshold + (2 * (n : Real)) * evenParityCoordinate n

def evenParityPairDiscrepancy (n : Nat) : Real :=
  evenParityPairMass n - (2 + 2 * (n : Real))

def evenParityPairEnergy (n : Nat) : Real :=
  2 * momentRoundThreshold * (momentRoundThreshold - 1) ^ 2 +
    (2 * (n : Real)) * evenParityCoordinate n * (evenParityCoordinate n - 1) ^ 2

theorem evenParityCoordinate_quadratic (n : Nat) (hn : 0 < n) :
    evenParityCoordinate n * (evenParityCoordinate n - 1) =
      (1 - 2 * momentRoundThreshold) / (2 * (n : Real)) := by
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  have hA : 0 < 1 - 2 * momentRoundThreshold := by
    have hh := momentRoundThreshold_bounds.2
    linarith
  have hRad : 0 <= 1 + 2 * (1 - 2 * momentRoundThreshold) / (n : Real) := by positivity
  have hRoot := Real.sq_sqrt hRad
  unfold evenParityCoordinate
  calc
    _ = (Real.sqrt (1 + 2 * (1 - 2 * momentRoundThreshold) / (n : Real))) ^ 2 / 4 - 1 / 4 := by ring
    _ = (1 + 2 * (1 - 2 * momentRoundThreshold) / (n : Real)) / 4 - 1 / 4 := by rw [hRoot]
    _ = _ := by field_simp [hN.ne']; ring

theorem evenParityCoordinate_gt_one (n : Nat) (hn : 0 < n) :
    1 < evenParityCoordinate n := by
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  have hA : 0 < 1 - 2 * momentRoundThreshold := by
    have hh := momentRoundThreshold_bounds.2
    linarith
  have hz : 0 < evenParityCoordinate n := by
    unfold evenParityCoordinate
    have hh := Real.sqrt_nonneg (1 + 2 * (1 - 2 * momentRoundThreshold) / (n : Real))
    linarith
  have hProduct := evenParityCoordinate_quadratic n hn
  have hRhs := div_pos hA (mul_pos (by norm_num : (0 : Real) < 2) hN)
  by_contra hNot
  have hNonpos := mul_nonpos_of_nonneg_of_nonpos hz.le (sub_nonpos.mpr (le_of_not_gt hNot))
  rw [hProduct] at hNonpos
  linarith only [hNonpos, hRhs]

theorem evenParityCoordinate_scaled_weight (n : Nat) (hn : 0 < n) :
    (2 * (n : Real)) * sharpParityModelWeight (evenParityCoordinate n) = 2 := by
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  have hA : 0 < 1 - 2 * momentRoundThreshold := by
    have hh := momentRoundThreshold_bounds.2
    linarith
  unfold sharpParityModelWeight
  calc
    _ = 4 * (n : Real) * (evenParityCoordinate n * (evenParityCoordinate n - 1)) /
        (1 - 2 * momentRoundThreshold) := by ring
    _ = _ := by rw [evenParityCoordinate_quadratic n hn]; field_simp [hN.ne', hA.ne']; ring

theorem evenParityPair_mass_scaled (n : Nat) (hn : 0 < n) :
    evenParityPairMass n = (2 * (n : Real)) * sharpParityModelMass (evenParityCoordinate n) := by
  unfold evenParityPairMass sharpParityModelMass
  calc
    _ = ((2 * (n : Real)) * sharpParityModelWeight (evenParityCoordinate n)) * momentRoundThreshold +
        (2 * (n : Real)) * evenParityCoordinate n := by rw [evenParityCoordinate_scaled_weight n hn]
    _ = _ := by ring

theorem evenParityPair_discrepancy_scaled (n : Nat) (hn : 0 < n) :
    evenParityPairDiscrepancy n =
      (2 * (n : Real)) * sharpParityModelDiscrepancy (evenParityCoordinate n) := by
  unfold evenParityPairDiscrepancy sharpParityModelDiscrepancy
  rw [evenParityPair_mass_scaled n hn]
  calc
    _ = (2 * (n : Real)) * sharpParityModelMass (evenParityCoordinate n) -
        ((2 * (n : Real)) * sharpParityModelWeight (evenParityCoordinate n) + 2 * (n : Real)) := by
      rw [evenParityCoordinate_scaled_weight n hn]
    _ = _ := by ring

theorem evenParityPair_energy_scaled (n : Nat) (hn : 0 < n) :
    evenParityPairEnergy n = (2 * (n : Real)) * sharpParityModelEnergy (evenParityCoordinate n) := by
  unfold evenParityPairEnergy sharpParityModelEnergy
  calc
    _ = ((2 * (n : Real)) * sharpParityModelWeight (evenParityCoordinate n)) *
        momentRoundThreshold * (momentRoundThreshold - 1) ^ 2 +
        (2 * (n : Real)) * evenParityCoordinate n * (evenParityCoordinate n - 1) ^ 2 := by
      rw [evenParityCoordinate_scaled_weight n hn]
    _ = _ := by ring

theorem evenParityPair_moment (n : Nat) (hn : 0 < n) :
    2 * momentRoundThreshold ^ 2 + (2 * (n : Real)) * evenParityCoordinate n ^ 2 =
      evenParityPairMass n := by
  calc
    _ = ((2 * (n : Real)) * sharpParityModelWeight (evenParityCoordinate n)) * momentRoundThreshold ^ 2 +
        (2 * (n : Real)) * evenParityCoordinate n ^ 2 := by rw [evenParityCoordinate_scaled_weight n hn]
    _ = (2 * (n : Real)) *
        (sharpParityModelWeight (evenParityCoordinate n) * momentRoundThreshold ^ 2 +
          evenParityCoordinate n ^ 2) := by ring
    _ = (2 * (n : Real)) * sharpParityModelMass (evenParityCoordinate n) := by
      rw [sharpParityModel_moment]
      rfl
    _ = _ := (evenParityPair_mass_scaled n hn).symm

theorem evenParityPair_mass_pos (n : Nat) (hn : 0 < n) :
    0 < evenParityPairMass n := by
  unfold evenParityPairMass
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  exact add_pos (mul_pos (by norm_num) momentRoundThreshold_bounds.1)
    (mul_pos (by linarith) (lt_trans (by norm_num) (evenParityCoordinate_gt_one n hn)))

theorem evenParityPair_discrepancy_neg (n : Nat) (hn : 0 < n) :
    evenParityPairDiscrepancy n < 0 := by
  rw [evenParityPair_discrepancy_scaled n hn]
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  exact mul_neg_of_pos_of_neg (by linarith)
    (sharpParityModel_discrepancy_neg _ (evenParityCoordinate_gt_one n hn))

theorem evenParityPair_exact_ratio (n : Nat) (hn : 0 < n) :
    evenParityPairMass n *
      (evenParityPairEnergy n - momentRoundThreshold * abs (evenParityPairDiscrepancy n)) =
      sharpParityCoefficient * evenParityCoordinate n * evenParityPairDiscrepancy n ^ 2 := by
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  have hScale : 0 < 2 * (n : Real) := by linarith
  rw [evenParityPair_mass_scaled n hn, evenParityPair_energy_scaled n hn,
    evenParityPair_discrepancy_scaled n hn, abs_mul, abs_of_pos hScale]
  calc
    _ = (2 * (n : Real)) ^ 2 * (sharpParityModelMass (evenParityCoordinate n) *
        (sharpParityModelEnergy (evenParityCoordinate n) -
          momentRoundThreshold * abs (sharpParityModelDiscrepancy (evenParityCoordinate n)))) := by ring
    _ = _ := by
      rw [sharpParityModel_exact_ratio _ (evenParityCoordinate_gt_one n hn)]
      ring

theorem evenParityCoordinate_lt_of_nat_bound (n : Nat) (hn : 0 < n) (q : Real) (hq : 1 < q)
    (hBound : (1 - 2 * momentRoundThreshold) / (2 * q * (q - 1)) < (n : Real)) :
    evenParityCoordinate n < q := by
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  have hDen : 0 < 2 * q * (q - 1) := mul_pos (by linarith) (sub_pos.mpr hq)
  have hCancel : ((1 - 2 * momentRoundThreshold) / (2 * q * (q - 1))) *
      (2 * q * (q - 1)) = 1 - 2 * momentRoundThreshold := by
    field_simp [(show 0 < q by linarith).ne', (sub_pos.mpr hq).ne']
  have hGap := mul_pos (sub_pos.mpr hBound) hDen
  have hScaled : (2 * (n : Real)) * (evenParityCoordinate n * (evenParityCoordinate n - 1)) =
      1 - 2 * momentRoundThreshold := by
    rw [evenParityCoordinate_quadratic n hn]
    field_simp [hN.ne']
  by_contra hNot
  have hz : q <= evenParityCoordinate n := le_of_not_gt hNot
  have hDiff := mul_nonneg (sub_nonneg.mpr hz)
    (show 0 <= evenParityCoordinate n + q - 1 by linarith)
  have hProduct := mul_nonneg (show 0 <= 2 * (n : Real) by linarith) hDiff
  nlinarith only [hCancel, hGap, hScaled, hProduct]

theorem evenParityPair_counterexample (c : Real) (hc : sharpParityCoefficient < c) :
    exists n : Nat, And (0 < n)
      (evenParityPairEnergy n <
        momentRoundThreshold * abs (evenParityPairDiscrepancy n) +
          c * evenParityPairDiscrepancy n ^ 2 / evenParityPairMass n) := by
  let q := c / sharpParityCoefficient
  have hG := sharpParityCoefficient_pos
  have hCancel : q * sharpParityCoefficient = c := by
    dsimp only [q]
    field_simp [hG.ne']
  have hq : 1 < q := by
    by_contra hn
    have hp := mul_nonneg hG.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith only [hp, hCancel, hc]
  choose n hn using exists_nat_gt (max (1 : Real)
    ((1 - 2 * momentRoundThreshold) / (2 * q * (q - 1))))
  have hRealN : 0 < (n : Real) := lt_trans (by norm_num)
    (lt_of_le_of_lt (le_max_left _ _) hn)
  have hN : 0 < n := by exact_mod_cast hRealN
  have hBound : (1 - 2 * momentRoundThreshold) / (2 * q * (q - 1)) < (n : Real) :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hz := evenParityCoordinate_lt_of_nat_bound n hN q hq hBound
  have hzc : sharpParityCoefficient * evenParityCoordinate n < c := by
    have hp := mul_pos hG (sub_pos.mpr hz)
    nlinarith only [hp, hCancel]
  have hM := evenParityPair_mass_pos n hN
  have hD := evenParityPair_discrepancy_neg n hN
  have hD2 : 0 < evenParityPairDiscrepancy n ^ 2 := sq_pos_of_neg hD
  have hExact := evenParityPair_exact_ratio n hN
  have hStrict := mul_pos (sub_pos.mpr hzc) hD2
  have hCancelM : (c * evenParityPairDiscrepancy n ^ 2 / evenParityPairMass n) *
      evenParityPairMass n = c * evenParityPairDiscrepancy n ^ 2 := by field_simp [hM.ne']
  refine Exists.intro n (And.intro hN ?_)
  by_contra hn
  have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) hM.le
  nlinarith only [hExact, hStrict, hCancelM, hp]


theorem evenParityCoordinate_excess_bounds (n : Nat) (hn : 0 < n) :
    And (0 < evenParityCoordinate n - 1)
      (evenParityCoordinate n - 1 < (1 - 2 * momentRoundThreshold) / (2 * (n : Real))) := by
  have hz := evenParityCoordinate_gt_one n hn
  have hq := evenParityCoordinate_quadratic n hn
  exact And.intro (sub_pos.mpr hz)
    (by nlinarith only [hq, sq_pos_of_pos (sub_pos.mpr hz)])

theorem evenParityPair_discrepancy_formula (n : Nat) (hn : 0 < n) :
    evenParityPairDiscrepancy n =
      (1 - 2 * momentRoundThreshold) / evenParityCoordinate n - sharpParityCarrier := by
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  have hz : 0 < evenParityCoordinate n := lt_trans (by norm_num) (evenParityCoordinate_gt_one n hn)
  have hProduct : (2 * (n : Real)) * (evenParityCoordinate n * (evenParityCoordinate n - 1)) =
      1 - 2 * momentRoundThreshold := by
    rw [evenParityCoordinate_quadratic n hn]
    field_simp [hN.ne']
  have hRatio : (2 * (n : Real)) * (evenParityCoordinate n - 1) =
      (1 - 2 * momentRoundThreshold) / evenParityCoordinate n := by
    field_simp [hz.ne']
    nlinarith only [hProduct]
  calc
    _ = (2 * (n : Real)) * (evenParityCoordinate n - 1) - sharpParityCarrier := by
      unfold evenParityPairDiscrepancy evenParityPairMass sharpParityCarrier
      ring
    _ = _ := by rw [hRatio]

theorem evenParityPair_discrepancy_location (n : Nat) (hn : 0 < n) :
    And (-sharpParityCarrier < evenParityPairDiscrepancy n)
      (evenParityPairDiscrepancy n < -1) := by
  have hz := evenParityCoordinate_gt_one n hn
  have hz0 : 0 < evenParityCoordinate n := by linarith
  have hA : 0 < 1 - 2 * momentRoundThreshold := by
    have hh := momentRoundThreshold_bounds.2
    linarith
  have hInv := div_pos hA hz0
  have hCancel : ((1 - 2 * momentRoundThreshold) / evenParityCoordinate n) *
      evenParityCoordinate n = 1 - 2 * momentRoundThreshold := by field_simp [hz0.ne']
  have hInvLt : (1 - 2 * momentRoundThreshold) / evenParityCoordinate n <
      1 - 2 * momentRoundThreshold := by
    by_contra hn
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) hz0.le
    have hGap := mul_pos hA (sub_pos.mpr hz)
    nlinarith only [hp, hGap, hCancel]
  rw [evenParityPair_discrepancy_formula n hn]
  constructor
  case left => linarith only [hInv]
  case right =>
    unfold sharpParityCarrier
    linarith only [hInvLt]

def evenParityWeights (n : Nat) (i : Fin 2) : Nat :=
  if i = 0 then 2 else 2 * n

def evenParityCoordinates (n : Nat) (i : Fin 2) : Real :=
  if i = 0 then momentRoundThreshold else evenParityCoordinate n

theorem evenParityWeights_even (n : Nat) (i : Fin 2) :
    Even (evenParityWeights n i) := by
  unfold evenParityWeights
  by_cases hi : i = 0
  case pos =>
    rw [if_pos hi]
    exact Exists.intro 1 (by norm_num)
  case neg =>
    rw [if_neg hi]
    exact Exists.intro n (by omega)

theorem evenParityCoordinates_nonneg (n : Nat) (hn : 0 < n) (i : Fin 2) :
    0 <= evenParityCoordinates n i := by
  unfold evenParityCoordinates
  by_cases hi : i = 0
  case pos =>
    rw [if_pos hi]
    exact momentRoundThreshold_bounds.1.le
  case neg =>
    rw [if_neg hi]
    have hz := evenParityCoordinate_gt_one n hn
    linarith

def EvenParityCoefficientAdmissible (c : Real) : Prop :=
  forall (m : Nat) (a : Fin m -> Nat) (y : Fin m -> Real),
    (forall i, Even (a i)) ->
    (forall i, 0 <= y i) ->
    let M := Finset.sum Finset.univ (fun i => (a i : Real) * y i)
    let D := M - Finset.sum Finset.univ
      (fun i => (a i : Real) * momentRoundIndicator momentRoundThreshold (y i))
    let E := Finset.sum Finset.univ (fun i => (a i : Real) * y i * (y i - 1) ^ 2)
    (Finset.sum Finset.univ (fun i => (a i : Real) * (y i) ^ 2) = M) ->
    0 < M ->
    momentRoundThreshold * abs D + c * D ^ 2 / M <= E

theorem evenParityCoefficientAdmissible_iff (c : Real) :
    EvenParityCoefficientAdmissible c <-> c <= sharpParityCoefficient := by
  constructor
  case mp =>
    intro hValid
    by_contra hNot
    have hc : sharpParityCoefficient < c := lt_of_not_ge hNot
    choose n hn using evenParityPair_counterexample c hc
    have hMoment :
        Finset.sum Finset.univ (fun i => (evenParityWeights n i : Real) *
          (evenParityCoordinates n i) ^ 2) =
        Finset.sum Finset.univ (fun i => (evenParityWeights n i : Real) *
          evenParityCoordinates n i) := by
      simpa [Fin.sum_univ_two, evenParityWeights, evenParityCoordinates,
        evenParityPairMass, Nat.cast_mul] using evenParityPair_moment n hn.1
    have hMass : 0 < Finset.sum Finset.univ (fun i =>
        (evenParityWeights n i : Real) * evenParityCoordinates n i) := by
      simpa [Fin.sum_univ_two, evenParityWeights, evenParityCoordinates,
        evenParityPairMass, Nat.cast_mul] using evenParityPair_mass_pos n hn.1
    have hBound := hValid 2 (evenParityWeights n) (evenParityCoordinates n)
      (evenParityWeights_even n) (evenParityCoordinates_nonneg n hn.1) hMoment hMass
    have hHigh : momentRoundThreshold <= evenParityCoordinate n := by
      have hd := momentRoundThreshold_bounds.2
      have hz := evenParityCoordinate_gt_one n hn.1
      linarith
    have hModelBound : momentRoundThreshold * abs (evenParityPairDiscrepancy n) +
        c * evenParityPairDiscrepancy n ^ 2 / evenParityPairMass n <= evenParityPairEnergy n := by
      simpa [Fin.sum_univ_two, evenParityWeights, evenParityCoordinates,
        evenParityPairMass, evenParityPairDiscrepancy, evenParityPairEnergy,
        momentRoundIndicator, hHigh, Nat.cast_mul] using hBound
    linarith only [hModelBound, hn.2]
  case mpr =>
    intro hc
    intro m a y _hEven hy
    dsimp only
    intro hMoment hMass
    let M := Finset.sum Finset.univ (fun i => (a i : Real) * y i)
    let D := M - Finset.sum Finset.univ
      (fun i => (a i : Real) * momentRoundIndicator momentRoundThreshold (y i))
    let E := Finset.sum Finset.univ (fun i => (a i : Real) * y i * (y i - 1) ^ 2)
    have hSharp := finiteWeightedParity_sharp_stability Finset.univ
      (fun i => (a i : Real)) y (fun i _ => Nat.cast_nonneg (a i))
      (fun i _ => hy i) hMoment hMass
    change sharpParityStabilityCost M D <= E at hSharp
    change momentRoundThreshold * abs D + c * D ^ 2 / M <= E
    unfold sharpParityStabilityCost at hSharp
    have hRatio : 0 <= D ^ 2 / M := div_nonneg (sq_nonneg D) hMass.le
    have hGain := mul_nonneg (sub_nonneg.mpr hc) hRatio
    have hAlgebra : (sharpParityCoefficient - c) * (D ^ 2 / M) =
        sharpParityCoefficient * D ^ 2 / M - c * D ^ 2 / M := by ring
    rw [hAlgebra] at hGain
    linarith only [hSharp, hGain]

end PrimeFactorOscillations
