/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.EvenDirectionalWeightTuning

/-! # The sharp directional coefficient region for even natural weights

All countermodels are finite moment profiles, not actual zeta zero sets.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def evenPositiveParityMass (n : Nat) (e : Real) : Real :=
  2 * positiveParityLow e + (2 * (n : Real)) * positiveParityHigh e

def evenPositiveParityDiscrepancy (n : Nat) (e : Real) : Real :=
  evenPositiveParityMass n e - 2 * (n : Real)

def evenPositiveParityEnergy (n : Nat) (e : Real) : Real :=
  2 * positiveParityLow e * (positiveParityLow e - 1) ^ 2 +
    (2 * (n : Real)) * positiveParityHigh e * (positiveParityHigh e - 1) ^ 2

def evenPositiveParityCoordinates (e : Real) (i : Fin 2) : Real :=
  if i = 0 then positiveParityLow e else positiveParityHigh e

theorem evenPositiveParity_mass_scaled (n : Nat) (e : Real)
    (hScale : (2 * (n : Real)) * positiveParityWeight e = 2) :
    evenPositiveParityMass n e = (2 * (n : Real)) * positiveParityMass e := by
  unfold evenPositiveParityMass positiveParityMass
  calc
    _ = ((2 * (n : Real)) * positiveParityWeight e) * positiveParityLow e +
        (2 * (n : Real)) * positiveParityHigh e := by rw [hScale]
    _ = _ := by ring

theorem evenPositiveParity_discrepancy_scaled (n : Nat) (e : Real)
    (hScale : (2 * (n : Real)) * positiveParityWeight e = 2) :
    evenPositiveParityDiscrepancy n e = (2 * (n : Real)) * positiveParityDiscrepancy e := by
  unfold evenPositiveParityDiscrepancy positiveParityDiscrepancy
  rw [evenPositiveParity_mass_scaled n e hScale]
  ring

theorem evenPositiveParity_energy_scaled (n : Nat) (e : Real)
    (hScale : (2 * (n : Real)) * positiveParityWeight e = 2) :
    evenPositiveParityEnergy n e = (2 * (n : Real)) * positiveParityEnergy e := by
  unfold evenPositiveParityEnergy positiveParityEnergy
  calc
    _ = ((2 * (n : Real)) * positiveParityWeight e) * positiveParityLow e *
        (positiveParityLow e - 1) ^ 2 +
        (2 * (n : Real)) * positiveParityHigh e * (positiveParityHigh e - 1) ^ 2 := by rw [hScale]
    _ = _ := by ring

theorem evenPositiveParity_moment (n : Nat) (e : Real)
    (he : And (0 < e) (e < 1 / 2))
    (hScale : (2 * (n : Real)) * positiveParityWeight e = 2) :
    2 * positiveParityLow e ^ 2 + (2 * (n : Real)) * positiveParityHigh e ^ 2 =
      evenPositiveParityMass n e := by
  calc
    _ = ((2 * (n : Real)) * positiveParityWeight e) * positiveParityLow e ^ 2 +
        (2 * (n : Real)) * positiveParityHigh e ^ 2 := by rw [hScale]
    _ = (2 * (n : Real)) *
        (positiveParityWeight e * positiveParityLow e ^ 2 + positiveParityHigh e ^ 2) := by ring
    _ = (2 * (n : Real)) * positiveParityMass e := by rw [positiveParity_moment e he]
    _ = _ := (evenPositiveParity_mass_scaled n e hScale).symm

theorem evenPositiveParity_mass_pos (n : Nat) (e : Real) (hn : 0 < n)
    (he : And (0 < e) (e < 1 / 2))
    (hScale : (2 * (n : Real)) * positiveParityWeight e = 2) :
    0 < evenPositiveParityMass n e := by
  rw [evenPositiveParity_mass_scaled n e hScale]
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  exact mul_pos (by linarith) (positiveParityMass_pos e he)

theorem evenPositiveParity_discrepancy_pos (n : Nat) (e : Real) (hn : 0 < n)
    (he : And (0 < e) (e < 1 / 2))
    (hScale : (2 * (n : Real)) * positiveParityWeight e = 2) :
    0 < evenPositiveParityDiscrepancy n e := by
  rw [evenPositiveParity_discrepancy_scaled n e hScale]
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  exact mul_pos (by linarith) (positiveParityDiscrepancy_pos e he)

theorem evenPositiveParity_mass_gt_weight (n : Nat) (e : Real) (hn : 0 < n)
    (he : And (0 < e) (e < 1 / 2)) :
    2 * (n : Real) < evenPositiveParityMass n e := by
  have hN : 0 < (n : Real) := by exact_mod_cast hn
  have hU := (positiveParityLow_bounds e he).1
  have hZ := positiveParityHigh_gt_one e he.1
  have hGap := mul_pos (show 0 < 2 * (n : Real) by linarith) (sub_pos.mpr hZ)
  unfold evenPositiveParityMass
  nlinarith only [hGap, hU]

theorem evenPositiveParity_exact_ratio (n : Nat) (e : Real)
    (he : And (0 < e) (e < 1 / 2))
    (hScale : (2 * (n : Real)) * positiveParityWeight e = 2) :
    evenPositiveParityMass n e *
      (evenPositiveParityEnergy n e - momentRoundThreshold * evenPositiveParityDiscrepancy n e) =
      positiveParityRatio e * evenPositiveParityDiscrepancy n e ^ 2 := by
  rw [evenPositiveParity_mass_scaled n e hScale, evenPositiveParity_energy_scaled n e hScale,
    evenPositiveParity_discrepancy_scaled n e hScale]
  calc
    _ = (2 * (n : Real)) ^ 2 * (positiveParityMass e *
        (positiveParityEnergy e - momentRoundThreshold * positiveParityDiscrepancy e)) := by ring
    _ = _ := by rw [positiveParity_exact_ratio e he]; ring

theorem evenPositiveParityCoordinates_nonneg (e : Real)
    (he : And (0 < e) (e < 1 / 2)) (i : Fin 2) :
    0 <= evenPositiveParityCoordinates e i := by
  unfold evenPositiveParityCoordinates
  by_cases hi : i = 0
  case pos => rw [if_pos hi]; exact (positiveParityLow_bounds e he).1.le
  case neg =>
    rw [if_neg hi]
    have hZ := positiveParityHigh_gt_one e he.1
    linarith only [hZ]

theorem evenPositiveParity_counterexamples (c : Real) (hc : positiveParityCoefficient < c) :
    exists N : Nat, And (0 < N) (forall n : Nat, N <= n ->
      exists e : Real, And (And (0 < e) (e < 1 / 2))
        (And ((2 * (n : Real)) * positiveParityWeight e = 2)
          (evenPositiveParityEnergy n e < momentRoundThreshold * evenPositiveParityDiscrepancy n e +
            c * evenPositiveParityDiscrepancy n e ^ 2 / evenPositiveParityMass n e))) := by
  choose N hN using positiveParityWeight_integral_scales c hc
  refine Exists.intro N (And.intro hN.1 ?_)
  intro n hn
  choose e he using hN.2 n hn
  have hnPos : 0 < n := lt_of_lt_of_le hN.1 hn
  have hM := evenPositiveParity_mass_pos n e hnPos he.1 he.2.1
  have hD := evenPositiveParity_discrepancy_pos n e hnPos he.1 he.2.1
  have hRatio := evenPositiveParity_exact_ratio n e he.1 he.2.1
  have hStrict := mul_pos (sub_pos.mpr he.2.2) (sq_pos_of_pos hD)
  have hCancel : (c * evenPositiveParityDiscrepancy n e ^ 2 / evenPositiveParityMass n e) *
      evenPositiveParityMass n e = c * evenPositiveParityDiscrepancy n e ^ 2 := by field_simp [hM.ne']
  refine Exists.intro e (And.intro he.1 (And.intro he.2.1 ?_))
  by_contra hh
  have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hh)) hM.le
  nlinarith only [hRatio, hStrict, hCancel, hp]

def EvenDirectionalParityCoefficientAdmissible (cp cm : Real) : Prop :=
  forall (m : Nat) (a : Fin m -> Nat) (y : Fin m -> Real),
    (forall i, Even (a i)) ->
    (forall i, 0 <= y i) ->
    let M := Finset.sum Finset.univ (fun i => (a i : Real) * y i)
    let D := M - Finset.sum Finset.univ
      (fun i => (a i : Real) * momentRoundIndicator momentRoundThreshold (y i))
    let E := Finset.sum Finset.univ (fun i => (a i : Real) * y i * (y i - 1) ^ 2)
    (Finset.sum Finset.univ (fun i => (a i : Real) * (y i) ^ 2) = M) ->
    0 < M ->
    momentRoundThreshold * abs D + (if 0 <= D then cp else cm) * D ^ 2 / M <= E

theorem evenDirectionalParityCoefficientAdmissible_iff (cp cm : Real) :
    EvenDirectionalParityCoefficientAdmissible cp cm <->
      And (cp <= positiveParityCoefficient) (cm <= sharpParityCoefficient) := by
  constructor
  case mp =>
    intro hValid
    constructor
    case left =>
      by_contra hh
      have hc : positiveParityCoefficient < cp := lt_of_not_ge hh
      choose N hN using evenPositiveParity_counterexamples cp hc
      choose e he using hN.2 N (le_refl N)
      let a : Fin 2 -> Nat := evenParityWeights N
      let y : Fin 2 -> Real := evenPositiveParityCoordinates e
      have hU := positiveParityLow_bounds e he.1
      have hZ := positiveParityHigh_gt_one e he.1.1
      have hMoment : Finset.sum Finset.univ (fun i => (a i : Real) * (y i) ^ 2) =
          Finset.sum Finset.univ (fun i => (a i : Real) * y i) := by
        simpa [Fin.sum_univ_two, a, y, evenParityWeights, evenPositiveParityCoordinates,
          evenPositiveParityMass, Nat.cast_mul] using evenPositiveParity_moment N e he.1 he.2.1
      have hMass : 0 < Finset.sum Finset.univ (fun i => (a i : Real) * y i) := by
        simpa [Fin.sum_univ_two, a, y, evenParityWeights, evenPositiveParityCoordinates,
          evenPositiveParityMass, Nat.cast_mul] using evenPositiveParity_mass_pos N e hN.1 he.1 he.2.1
      have hBound := hValid 2 a y (evenParityWeights_even N)
        (evenPositiveParityCoordinates_nonneg e he.1) hMoment hMass
      have hLow : Not (momentRoundThreshold <= positiveParityLow e) := not_le_of_gt hU.2
      have hHigh : momentRoundThreshold <= positiveParityHigh e := by
        have hd := momentRoundThreshold_bounds.2
        linarith only [hd, hZ]
      have hD : 0 < 2 * positiveParityLow e + (2 * (N : Real)) * positiveParityHigh e -
          2 * (N : Real) := evenPositiveParity_discrepancy_pos N e hN.1 he.1 he.2.1
      have hModel : momentRoundThreshold * evenPositiveParityDiscrepancy N e +
          cp * evenPositiveParityDiscrepancy N e ^ 2 / evenPositiveParityMass N e <=
            evenPositiveParityEnergy N e := by
        simpa [Fin.sum_univ_two, a, y, evenParityWeights, evenPositiveParityCoordinates,
          evenPositiveParityMass, evenPositiveParityDiscrepancy, evenPositiveParityEnergy,
          momentRoundIndicator, hLow, hHigh, Nat.cast_mul, hD.le, abs_of_pos hD] using hBound
      linarith only [hModel, he.2.2]
    case right =>
      by_contra hh
      have hc : sharpParityCoefficient < cm := lt_of_not_ge hh
      choose n hn using evenParityPair_counterexample cm hc
      let a : Fin 2 -> Nat := evenParityWeights n
      let y : Fin 2 -> Real := evenParityCoordinates n
      have hMoment : Finset.sum Finset.univ (fun i => (a i : Real) * (y i) ^ 2) =
          Finset.sum Finset.univ (fun i => (a i : Real) * y i) := by
        simpa [Fin.sum_univ_two, a, y, evenParityWeights, evenParityCoordinates,
          evenParityPairMass, Nat.cast_mul] using evenParityPair_moment n hn.1
      have hMass : 0 < Finset.sum Finset.univ (fun i => (a i : Real) * y i) := by
        simpa [Fin.sum_univ_two, a, y, evenParityWeights, evenParityCoordinates,
          evenParityPairMass, Nat.cast_mul] using evenParityPair_mass_pos n hn.1
      have hBound := hValid 2 a y (evenParityWeights_even n)
        (evenParityCoordinates_nonneg n hn.1) hMoment hMass
      have hHigh : momentRoundThreshold <= evenParityCoordinate n := by
        have hd := momentRoundThreshold_bounds.2
        have hz := evenParityCoordinate_gt_one n hn.1
        linarith only [hd, hz]
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
    intro hCoeffs m a y _hEven hy
    dsimp only
    intro hMoment hMass
    have hReal := (directionalParityCoefficientAdmissible_iff cp cm).mpr hCoeffs
    exact hReal m (fun i => (a i : Real)) y (fun i => Nat.cast_nonneg _) hy hMoment hMass

theorem evenDirectionalParityCoefficientAdmissible_iff_real (cp cm : Real) :
    EvenDirectionalParityCoefficientAdmissible cp cm <-> DirectionalParityCoefficientAdmissible cp cm :=
  (evenDirectionalParityCoefficientAdmissible_iff cp cm).trans
    (directionalParityCoefficientAdmissible_iff cp cm).symm

end PrimeFactorOscillations
