/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.EvenIntegralParityOptimality

/-! # Directional compensated parity stability -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations


def positiveParityCoefficient : Real :=
  (1 - 2 * momentRoundThreshold) ^ 2 * (1 + momentRoundThreshold)

def directionalParityStabilityCost (mass discrepancy : Real) : Real :=
  momentRoundThreshold * abs discrepancy +
    (if 0 <= discrepancy then positiveParityCoefficient else sharpParityCoefficient) *
      discrepancy ^ 2 / mass

theorem positiveParityCoefficient_gain :
    positiveParityCoefficient = sharpParityCoefficient + 4 * momentRoundThreshold ^ 3 := by
  unfold positiveParityCoefficient sharpParityCoefficient
  ring

theorem positiveParityCoefficient_gt_sharp : sharpParityCoefficient < positiveParityCoefficient := by
  rw [positiveParityCoefficient_gain]
  have hp : 0 < 4 * momentRoundThreshold ^ 3 := by
    have hd := momentRoundThreshold_bounds.1
    positivity
  linarith

theorem positiveParityCoefficient_pos : 0 < positiveParityCoefficient :=
  lt_trans sharpParityCoefficient_pos positiveParityCoefficient_gt_sharp

theorem positiveParity_square_certificate (d y : Real)
    (hd : And (0 <= d) (d < 1 / 2)) (hy : 1 <= y) :
    (1 + d) * compensatedParityTransport d 1 y ^ 2 <=
      y ^ 2 * compensatedParityResidual d 1 y := by
  classical
  have hdy : d <= y := by linarith
  have hA : 0 <= 1 - 4 * d ^ 2 := by
    nlinarith only [mul_nonneg (show 0 <= 1 - 2 * d by linarith)
      (show 0 <= 1 + 2 * d by linarith)]
  have hInner : 0 <= y ^ 2 + (1 + d) * (1 - 4 * d ^ 2) * y +
      (1 - 2 * d) ^ 2 * (1 + d) := by
    have hOne : 0 <= 1 + d := by linarith
    exact add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hOne hA)
      (show 0 <= y by linarith))) (mul_nonneg (sq_nonneg _) hOne)
  have hPoly :
      y ^ 2 * (y + d) - (1 + d) * (2 * d * y + 1 - 2 * d) ^ 2 =
      (y - 1) * (y ^ 2 + (1 + d) * (1 - 4 * d ^ 2) * y +
        (1 - 2 * d) ^ 2 * (1 + d)) := by ring
  have hBase : (1 + d) * (2 * d * y + 1 - 2 * d) ^ 2 <= y ^ 2 * (y + d) := by
    have hh := mul_nonneg (show 0 <= y - 1 by linarith) hInner
    nlinarith only [hPoly, hh]
  have hScaled := _root_.mul_le_mul_of_nonneg_right hBase (sq_nonneg (y - 1))
  have hR : compensatedParityResidual d 1 y = (y + d) * (y - 1) ^ 2 := by
    unfold compensatedParityResidual momentRoundIndicator
    rw [ite_eq_left hdy]
    ring
  have hK : compensatedParityTransport d 1 y =
      (2 * d * y + 1 - 2 * d) * (y - 1) := by
    unfold compensatedParityTransport momentRoundIndicator
    rw [ite_eq_left hdy]
    ring
  rw [hR, hK]
  nlinarith only [hScaled]

theorem positiveParity_quadratic_nonneg (y u : Real) (hy : 0 <= y) (hu : 0 <= u) :
    0 <= ((1 + momentRoundThreshold) / 4) * y ^ 2 * u ^ 2 -
      (1 + momentRoundThreshold) * u * compensatedParityTransport momentRoundThreshold 1 y +
      compensatedParityResidual momentRoundThreshold 1 y := by
  have hd : And (1 / 4 <= momentRoundThreshold) (momentRoundThreshold < 1 / 2) :=
    And.intro momentRoundThreshold_gt_quarter.le momentRoundThreshold_bounds.2
  have hOne : 0 < 1 + momentRoundThreshold := by
    have hh := momentRoundThreshold_bounds.1
    linarith
  by_cases hLow : y <= 1
  case pos =>
    have hK := compensatedParityTransport_nonpos_below_one momentRoundThreshold 1 y
      hd momentRoundThreshold_equation (And.intro hy hLow) (Or.inl rfl)
    have hR : 0 <= compensatedParityResidual momentRoundThreshold 1 y := by
      simpa using compensatedParity_quadratic_nonneg y 1 0 hy (Or.inl rfl)
    have hFirst : 0 <= ((1 + momentRoundThreshold) / 4) * y ^ 2 * u ^ 2 := by positivity
    have hMiddle := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hOne.le hu) hK
    nlinarith only [hFirst, hMiddle, hR]
  case neg =>
    have hyHigh : 1 <= y := le_of_lt (lt_of_not_ge hLow)
    have hCert := positiveParity_square_certificate momentRoundThreshold y
      (And.intro momentRoundThreshold_bounds.1.le hd.2) hyHigh
    have hScaled := _root_.mul_le_mul_of_nonneg_left hCert hOne.le
    have hSquare := sq_nonneg
      ((1 + momentRoundThreshold) * y ^ 2 * u / 2 -
        (1 + momentRoundThreshold) * compensatedParityTransport momentRoundThreshold 1 y)
    have hProduct : 0 <= (1 + momentRoundThreshold) * y ^ 2 *
        (((1 + momentRoundThreshold) / 4) * y ^ 2 * u ^ 2 -
          (1 + momentRoundThreshold) * u * compensatedParityTransport momentRoundThreshold 1 y +
          compensatedParityResidual momentRoundThreshold 1 y) := by
      nlinarith only [hScaled, hSquare]
    have hPositive : 0 < (1 + momentRoundThreshold) * y ^ 2 :=
      mul_pos hOne (by nlinarith only [hyHigh])
    exact nonneg_of_mul_nonneg_right hProduct hPositive

theorem finiteWeightedParity_positive_quadratic {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (u : Real) (hu : 0 <= u)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i)) :
    0 <= ((1 + momentRoundThreshold) / 4) * Finset.sum S (fun i => a i * y i) * u ^ 2 -
      (1 + momentRoundThreshold) * u * (1 - 2 * momentRoundThreshold) *
        (Finset.sum S (fun i => a i * y i) -
          Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) +
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
      momentRoundThreshold *
        (Finset.sum S (fun i => a i * y i) -
          Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) := by
  have hH : Finset.sum S (fun i => a i * y i * (y i - 1)) = 0 := by
    calc
      _ = Finset.sum S (fun i => a i * (y i) ^ 2) -
          Finset.sum S (fun i => a i * y i) := by
        rw [<- Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hMoment]; ring
  have hG : Finset.sum S (fun i => a i *
      (2 * y i - (y i) ^ 2 - momentRoundIndicator momentRoundThreshold (y i))) =
      Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i)) := by
    calc
      _ = Finset.sum S (fun i => 2 * (a i * y i) - a i * (y i) ^ 2 -
          a i * momentRoundIndicator momentRoundThreshold (y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum, hMoment]
        ring
  have hPacket :
      Finset.sum S (fun i => a i * (((1 + momentRoundThreshold) / 4) * (y i) ^ 2 * u ^ 2 -
        (1 + momentRoundThreshold) * u * compensatedParityTransport momentRoundThreshold 1 (y i) +
        compensatedParityResidual momentRoundThreshold 1 (y i))) =
      ((1 + momentRoundThreshold) / 4) * Finset.sum S (fun i => a i * y i) * u ^ 2 -
        (1 + momentRoundThreshold) * u * (1 - 2 * momentRoundThreshold) *
          (Finset.sum S (fun i => a i * y i) -
            Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) +
        Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
        momentRoundThreshold *
          (Finset.sum S (fun i => a i * y i) -
            Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) := by
    calc
      _ = Finset.sum S (fun i =>
          ((((1 + momentRoundThreshold) / 4) * (a i * (y i) ^ 2)) * u ^ 2 - (1 + momentRoundThreshold) * u * (a i * y i * (y i - 1))) -
          ((1 + momentRoundThreshold) * u * (1 - 2 * momentRoundThreshold)) * (a i *
            (2 * y i - (y i) ^ 2 - momentRoundIndicator momentRoundThreshold (y i))) +
          a i * y i * (y i - 1) ^ 2 -
          (momentRoundThreshold) * (a i *
            (2 * y i - (y i) ^ 2 - momentRoundIndicator momentRoundThreshold (y i)))) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold compensatedParityTransport compensatedParityResidual
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          <- Finset.mul_sum, hG, hH, mul_zero, sub_zero]
        have hc : Finset.sum S (fun i =>
            ((1 + momentRoundThreshold) / 4) * (a i * (y i) ^ 2) * u ^ 2) =
            ((1 + momentRoundThreshold) / 4) * Finset.sum S (fun i => a i * y i) * u ^ 2 := by
          calc
            _ = Finset.sum S (fun i => (((1 + momentRoundThreshold) / 4) * u ^ 2) *
                (a i * (y i) ^ 2)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
            _ = (((1 + momentRoundThreshold) / 4) * u ^ 2) *
                Finset.sum S (fun i => a i * (y i) ^ 2) := by rw [Finset.mul_sum]
            _ = _ := by rw [hMoment]; ring
        rw [hc]
  have hSum := Finset.sum_nonneg (fun i hi =>
    mul_nonneg (ha i hi) (positiveParity_quadratic_nonneg (y i) u (hy i hi) hu))
  rw [hPacket] at hSum
  exact hSum



theorem finiteWeightedParity_positive_stability {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hDiscrepancy : 0 <= Finset.sum S (fun i => a i * y i) -
      Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) :
    momentRoundThreshold * (Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) +
      positiveParityCoefficient * (Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) ^ 2 /
        Finset.sum S (fun i => a i * y i) <=
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  let M := Finset.sum S (fun i => a i * y i)
  let D := M - Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))
  let E := Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2)
  let u := 2 * (1 - 2 * momentRoundThreshold) * D / M
  have hM : 0 < M := hMass
  have hD : 0 <= D := hDiscrepancy
  have hu : 0 <= u := by
    dsimp only [u]
    exact div_nonneg (mul_nonneg (by
      have hd := momentRoundThreshold_bounds.2
      linarith) hD) hM.le
  have hQuad := finiteWeightedParity_positive_quadratic S a y u hu ha hy hMoment
  change 0 <= ((1 + momentRoundThreshold) / 4) * M * u ^ 2 -
    (1 + momentRoundThreshold) * u * (1 - 2 * momentRoundThreshold) * D +
    E - momentRoundThreshold * D at hQuad
  have hAlgebra :
      M * (((1 + momentRoundThreshold) / 4) * M * u ^ 2 -
        (1 + momentRoundThreshold) * u * (1 - 2 * momentRoundThreshold) * D +
        E - momentRoundThreshold * D) =
      M * (E - momentRoundThreshold * D) - positiveParityCoefficient * D ^ 2 := by
    dsimp only [u]
    unfold positiveParityCoefficient
    field_simp [hM.ne']
    ring
  have hNonneg := mul_nonneg hM.le hQuad
  rw [hAlgebra] at hNonneg
  have hScaled : positiveParityCoefficient * D ^ 2 <= M * (E - momentRoundThreshold * D) := by
    linarith only [hNonneg]
  have hDiv : positiveParityCoefficient * D ^ 2 / M <= E - momentRoundThreshold * D := by
    have he : (positiveParityCoefficient * D ^ 2 / M) * M = positiveParityCoefficient * D ^ 2 := by
      field_simp [hM.ne']
    by_contra hn
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hM
    nlinarith only [he, hp, hScaled]
  change momentRoundThreshold * D + positiveParityCoefficient * D ^ 2 / M <= E
  linarith only [hDiv]

theorem finiteWeightedParity_directional_stability {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    directionalParityStabilityCost (Finset.sum S (fun i => a i * y i))
      (Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) <=
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  by_cases hD : 0 <= Finset.sum S (fun i => a i * y i) -
      Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))
  case pos =>
    simpa only [directionalParityStabilityCost, if_pos hD, abs_of_nonneg hD] using
      finiteWeightedParity_positive_stability S a y ha hy hMoment hMass hD
  case neg =>
    simpa only [directionalParityStabilityCost, if_neg hD, sharpParityStabilityCost] using
      finiteWeightedParity_sharp_stability S a y ha hy hMoment hMass

theorem directionalParityStabilityCost_gain (mass D : Real) :
    directionalParityStabilityCost mass D = sharpParityStabilityCost mass D +
      4 * momentRoundThreshold ^ 3 * (max D 0) ^ 2 / mass := by
  by_cases hD : 0 <= D
  case pos =>
    simp only [directionalParityStabilityCost, sharpParityStabilityCost,
      if_pos hD, max_eq_left hD, positiveParityCoefficient_gain]
    ring
  case neg =>
    have hNonpos : D <= 0 := (lt_of_not_ge hD).le
    simp [directionalParityStabilityCost, sharpParityStabilityCost, if_neg hD, max_eq_right hNonpos]

theorem directionalParityStabilityCost_dominates (mass D : Real) (hMass : 0 < mass) :
    sharpParityStabilityCost mass D <= directionalParityStabilityCost mass D := by
  rw [directionalParityStabilityCost_gain]
  have hGain : 0 <= 4 * momentRoundThreshold ^ 3 * (max D 0) ^ 2 / mass := by
    have hd := momentRoundThreshold_bounds.1
    positivity
  linarith only [hGain]

theorem finiteWeightedParity_directional_stability_scaled {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> 0 <= x i)
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i)) :
    directionalParityStabilityCost (Finset.sum S (fun i => a i * x i) / t)
      (Finset.sum S (fun i => a i * x i) / t -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t))) *
      t ^ 3 <= Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
  have hNormalized : Finset.sum S (fun i => a i * (x i / t) ^ 2) =
      Finset.sum S (fun i => a i * (x i / t)) := by
    calc
      _ = Finset.sum S (fun i => a i * (x i) ^ 2) / t ^ 2 := by
        simp only [div_pow]
        exact finiteWeighted_div_sum S a (fun i => (x i) ^ 2) (t ^ 2)
      _ = Finset.sum S (fun i => a i * x i) / t := by
        rw [hMoment]
        field_simp [ht.ne']
      _ = _ := (finiteWeighted_div_sum S a x t).symm
  have hNormalizedMass : 0 < Finset.sum S (fun i => a i * (x i / t)) := by
    rw [finiteWeighted_div_sum]
    exact div_pos hMass ht
  have hCost := finiteWeightedParity_directional_stability S a (fun i => x i / t)
    ha (fun i hi => div_nonneg (hx i hi) (le_of_lt ht)) hNormalized hNormalizedMass
  rw [finiteWeighted_div_sum] at hCost
  have hScaled := _root_.mul_le_mul_of_nonneg_right hCost (le_of_lt (pow_pos ht 3))
  have hEnergy : t ^ 3 * Finset.sum S (fun i => a i * (x i / t) * (x i / t - 1) ^ 2) =
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := congrArg (fun q : Real => a i * q) (finiteWeighted_rescale_energy (x i) t ht)
    nlinarith only [h]
  nlinarith only [hScaled, hEnergy]

theorem threeLineWeightedDirectionalParityStability_charge {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i)) :
    threeLineCharge * Finset.sum S a +
      threeLineSizeBiasedProfile t * Finset.sum S (fun i => a i * x i) +
      threeLineParityCubicCoefficient * t ^ 3 *
        directionalParityStabilityCost (Finset.sum S (fun i => a i * x i) / t)
          (Finset.sum S (fun i => a i * x i) / t -
            Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t))) <=
      Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) := by
  have hCost := finiteWeightedParity_directional_stability_scaled S a x t ht ha
    (fun i hi => (hx i hi).1) hMoment hMass
  have hTau := threeLineParityCubicCoefficient_pos
  have hScaled := _root_.mul_le_mul_of_nonneg_left hCost (le_of_lt hTau)
  have hFloor : threeLineParityCubicCoefficient *
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) <=
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2 * threeLineSizeBiasedRemainder (x i) t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hKernel := threeLineSizeBiasedRemainder_ge_tau (x i) t (hx i hi).1 (hx i hi).2
      (le_of_lt ht) htMax
    have hNonneg : 0 <= a i * x i * (x i - t) ^ 2 :=
      mul_nonneg (mul_nonneg (ha i hi) (hx i hi).1) (sq_nonneg _)
    have hProduct := _root_.mul_le_mul_of_nonneg_left hKernel hNonneg
    nlinarith only [hProduct]
  have hLedger := threeLineWeightedKernel_ledger S a x t (by linarith)
    (fun i hi => (hx i hi).2) hMoment
  nlinarith only [hScaled, hFloor, hLedger]


end PrimeFactorOscillations
