/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThreeLineFixedScaleOptimality

/-! # Quantitative stability of the compensated parity bound -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def compensatedParityResidual (d s y : Real) : Real :=
  y * (y - 1) ^ 2 - s * d *
    (2 * y - y ^ 2 - momentRoundIndicator d y)

def compensatedParityTransport (d s y : Real) : Real :=
  y * (y - 1) + s * (1 - 2 * d) *
    (2 * y - y ^ 2 - momentRoundIndicator d y)

theorem compensatedParity_positive_high (d y : Real)
    (hd : And (1 / 4 <= d) (d < 1 / 2))
    (hRoot : 2 * d ^ 2 - 4 * d + 1 = 0) (hy : d <= y) :
    compensatedParityTransport d 1 y ^ 2 <= 4 * y * compensatedParityResidual d 1 y := by
  classical
  have hy0 : 0 <= y := by linarith
  have hd0 : 0 <= d := by linarith
  have hInside : 2 * y - (2 * d * y + 1 - 2 * d) =
      (2 - 2 * d) * (y - d) := by nlinarith only [hRoot]
  have hp0 : 0 <= 2 * d * y + 1 - 2 * d := by
    nlinarith only [hd.2, mul_nonneg hd0 hy0]
  have hpMax : 2 * d * y + 1 - 2 * d <= 2 * y := by
    have hMul := mul_nonneg (show 0 <= 2 - 2 * d by linarith) (sub_nonneg.mpr hy)
    nlinarith only [hInside, hMul]
  have hQuad : (2 * d * y + 1 - 2 * d) ^ 2 <= 4 * y * (y + d) := by
    have hMul := mul_nonneg (sub_nonneg.mpr hpMax)
      (show 0 <= 2 * y + (2 * d * y + 1 - 2 * d) by linarith)
    nlinarith [mul_nonneg hy0 hd0]
  have hScaled := _root_.mul_le_mul_of_nonneg_right hQuad (sq_nonneg (y - 1))
  have hR : compensatedParityResidual d 1 y = (y + d) * (y - 1) ^ 2 := by
    unfold compensatedParityResidual momentRoundIndicator
    rw [ite_eq_left hy]
    ring
  have hK : compensatedParityTransport d 1 y =
      (2 * d * y + 1 - 2 * d) * (y - 1) := by
    unfold compensatedParityTransport momentRoundIndicator
    rw [ite_eq_left hy]
    ring
  rw [hR, hK]
  nlinarith only [hScaled]

theorem compensatedParity_positive_low (d y : Real)
    (hd : And (1 / 4 <= d) (d < 1 / 2))
    (hRoot : 2 * d ^ 2 - 4 * d + 1 = 0) (hy0 : 0 <= y) (hy : y < d) :
    compensatedParityTransport d 1 y ^ 2 <= 4 * y * compensatedParityResidual d 1 y := by
  classical
  have hyD : 0 <= d - y := by linarith
  have hdSq : d ^ 2 <= 1 := by nlinarith
  have hInside : d ^ 2 * (d - y) <= 2 - 2 * d - y := by
    have hMul := _root_.mul_le_mul_of_nonneg_right hdSq hyD
    nlinarith only [hMul, hd.2]
  have hProduct := mul_nonneg hyD (sub_nonneg.mpr hInside)
  have hQuad : (2 * d * (y - d)) ^ 2 <=
      4 * ((d - y) * (2 - 2 * d - y)) := by
    nlinarith only [hProduct]
  have hScaled := _root_.mul_le_mul_of_nonneg_right hQuad (sq_nonneg y)
  have hR : compensatedParityResidual d 1 y =
      y * ((d - y) * (2 - 2 * d - y)) := by
    have hPoly : (y - 1) ^ 2 - d * (2 - y) =
        (d - y) * (2 - 2 * d - y) := by nlinarith only [hRoot]
    unfold compensatedParityResidual momentRoundIndicator
    rw [ite_eq_right (not_le.mpr hy)]
    calc
      _ = y * ((y - 1) ^ 2 - d * (2 - y)) := by ring
      _ = _ := by rw [hPoly]
  have hK : compensatedParityTransport d 1 y = y * (2 * d * (y - d)) := by
    have hPoly : y - 1 + (1 - 2 * d) * (2 - y) =
        2 * d * (y - d) := by nlinarith only [hRoot]
    unfold compensatedParityTransport momentRoundIndicator
    rw [ite_eq_right (not_le.mpr hy)]
    calc
      _ = y * (y - 1 + (1 - 2 * d) * (2 - y)) := by ring
      _ = _ := by rw [hPoly]
  rw [hR, hK]
  nlinarith only [hScaled]

theorem compensatedParity_negative_high (d y : Real)
    (hd : And (1 / 4 <= d) (d < 1 / 2))
    (hRoot : 2 * d ^ 2 - 4 * d + 1 = 0) (hy : d <= y) :
    compensatedParityTransport d (-1) y ^ 2 <=
      4 * y * compensatedParityResidual d (-1) y := by
  classical
  have hInside : (2 - 2 * d) * y - (1 - 2 * d) =
      (2 - 2 * d) * (y - d) := by nlinarith only [hRoot]
  have hCoeff : (2 - 2 * d) ^ 2 = 2 := by nlinarith only [hRoot]
  have hR : compensatedParityResidual d (-1) y = (y - d) * (y - 1) ^ 2 := by
    unfold compensatedParityResidual momentRoundIndicator
    rw [ite_eq_left hy]
    ring
  have hK : compensatedParityTransport d (-1) y =
      (2 - 2 * d) * (y - d) * (y - 1) := by
    unfold compensatedParityTransport momentRoundIndicator
    rw [ite_eq_left hy]
    calc
      _ = (y - 1) * ((2 - 2 * d) * y - (1 - 2 * d)) := by ring
      _ = _ := by rw [hInside]; ring
  have hNonneg : 0 <= compensatedParityResidual d (-1) y := by
    rw [hR]
    exact mul_nonneg (sub_nonneg.mpr hy) (sq_nonneg (y - 1))
  calc
    _ = (2 - 2 * d) ^ 2 * (y - d) ^ 2 * (y - 1) ^ 2 := by rw [hK]; ring
    _ = 2 * (y - d) * compensatedParityResidual d (-1) y := by rw [hCoeff, hR]; ring
    _ <= _ := _root_.mul_le_mul_of_nonneg_right (by linarith [hd.1]) hNonneg

theorem compensatedParity_negative_low (d y : Real)
    (hd : And (1 / 4 <= d) (d < 1 / 2))
    (hRoot : 2 * d ^ 2 - 4 * d + 1 = 0) (hy0 : 0 <= y) (hy : y < d) :
    compensatedParityTransport d (-1) y ^ 2 <=
      4 * y * compensatedParityResidual d (-1) y := by
  classical
  have hQ : 1 <= (y - 1) ^ 2 + d * (2 - y) := by
    have hMul := mul_nonneg (show 0 <= d - y by linarith) (show 0 <= 2 - y by linarith)
    nlinarith only [hMul]
  have hVLow : -2 <= (2 - 2 * d) * y + 4 * d - 3 := by
    have hMul := mul_nonneg (show 0 <= 2 - 2 * d by linarith) hy0
    nlinarith only [hMul, hd.1]
  have hVHigh : (2 - 2 * d) * y + 4 * d - 3 <= 0 := by
    have hMul := mul_nonneg (show 0 <= 2 - 2 * d by linarith) (show 0 <= d - y by linarith)
    nlinarith only [hMul, hRoot, hd.2]
  have hQuad : ((2 - 2 * d) * y + 4 * d - 3) ^ 2 <=
      4 * ((y - 1) ^ 2 + d * (2 - y)) := by
    have hMul := mul_nonneg
      (show 0 <= ((2 - 2 * d) * y + 4 * d - 3) + 2 by linarith)
      (show 0 <= 2 - ((2 - 2 * d) * y + 4 * d - 3) by linarith)
    nlinarith only [hMul, hQ]
  have hScaled := _root_.mul_le_mul_of_nonneg_right hQuad (sq_nonneg y)
  have hR : compensatedParityResidual d (-1) y =
      y * ((y - 1) ^ 2 + d * (2 - y)) := by
    unfold compensatedParityResidual momentRoundIndicator
    rw [ite_eq_right (not_le.mpr hy)]
    ring
  have hK : compensatedParityTransport d (-1) y =
      y * ((2 - 2 * d) * y + 4 * d - 3) := by
    unfold compensatedParityTransport momentRoundIndicator
    rw [ite_eq_right (not_le.mpr hy)]
    ring
  rw [hR, hK]
  nlinarith only [hScaled]

theorem compensatedParity_transport_square (y s : Real) (hy : 0 <= y)
    (hs : Or (s = 1) (s = -1)) :
    compensatedParityTransport momentRoundThreshold s y ^ 2 <=
      4 * y * compensatedParityResidual momentRoundThreshold s y := by
  have hd : And (1 / 4 <= momentRoundThreshold) (momentRoundThreshold < 1 / 2) :=
    And.intro (le_of_lt momentRoundThreshold_gt_quarter) momentRoundThreshold_bounds.2
  rcases hs with hs | hs
  case inl =>
    subst s
    by_cases hCut : momentRoundThreshold <= y
    case pos => exact compensatedParity_positive_high _ _ hd momentRoundThreshold_equation hCut
    case neg => exact compensatedParity_positive_low _ _ hd momentRoundThreshold_equation hy (lt_of_not_ge hCut)
  case inr =>
    subst s
    by_cases hCut : momentRoundThreshold <= y
    case pos => exact compensatedParity_negative_high _ _ hd momentRoundThreshold_equation hCut
    case neg => exact compensatedParity_negative_low _ _ hd momentRoundThreshold_equation hy (lt_of_not_ge hCut)

theorem compensatedParity_quadratic_nonneg (y s u : Real) (hy : 0 <= y)
    (hs : Or (s = 1) (s = -1)) :
    0 <= y * u ^ 2 - u * compensatedParityTransport momentRoundThreshold s y +
      compensatedParityResidual momentRoundThreshold s y := by
  by_cases hyZero : y = 0
  case pos =>
    subst y
    simp [compensatedParityTransport, compensatedParityResidual, momentRoundIndicator,
      not_le_of_gt momentRoundThreshold_bounds.1]
  case neg =>
    have hyPos : 0 < y := lt_of_le_of_ne hy (Ne.symm hyZero)
    have hCertificate := compensatedParity_transport_square y s hy hs
    have hSquare := sq_nonneg (2 * y * u - compensatedParityTransport momentRoundThreshold s y)
    have hProduct : 0 <= 4 * y * (y * u ^ 2 -
        u * compensatedParityTransport momentRoundThreshold s y +
        compensatedParityResidual momentRoundThreshold s y) := by
      nlinarith only [hCertificate, hSquare]
    by_contra hNot
    have hNegative := lt_of_not_ge hNot
    nlinarith only [hProduct, mul_neg_of_pos_of_neg (show 0 < 4 * y by linarith) hNegative]


def compensatedParityStabilityCost (mass discrepancy : Real) : Real :=
  momentRoundThreshold * abs discrepancy +
    (1 - 2 * momentRoundThreshold) ^ 2 * discrepancy ^ 2 / (4 * mass)

theorem finiteWeightedParity_quadratic {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (s u : Real) (hs : Or (s = 1) (s = -1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i)) :
    0 <= Finset.sum S (fun i => a i * y i) * u ^ 2 -
      u * s * (1 - 2 * momentRoundThreshold) *
        (Finset.sum S (fun i => a i * y i) -
          Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) +
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
      s * momentRoundThreshold *
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
      Finset.sum S (fun i => a i * (y i * u ^ 2 -
        u * compensatedParityTransport momentRoundThreshold s (y i) +
        compensatedParityResidual momentRoundThreshold s (y i))) =
      Finset.sum S (fun i => a i * y i) * u ^ 2 -
        u * s * (1 - 2 * momentRoundThreshold) *
          (Finset.sum S (fun i => a i * y i) -
            Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) +
        Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
        s * momentRoundThreshold *
          (Finset.sum S (fun i => a i * y i) -
            Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) := by
    calc
      _ = Finset.sum S (fun i =>
          ((a i * y i) * u ^ 2 - u * (a i * y i * (y i - 1))) -
          (u * s * (1 - 2 * momentRoundThreshold)) * (a i *
            (2 * y i - (y i) ^ 2 - momentRoundIndicator momentRoundThreshold (y i))) +
          a i * y i * (y i - 1) ^ 2 -
          (s * momentRoundThreshold) * (a i *
            (2 * y i - (y i) ^ 2 - momentRoundIndicator momentRoundThreshold (y i)))) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold compensatedParityTransport compensatedParityResidual
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_mul, <- Finset.mul_sum, hG, hH, mul_zero, sub_zero]
  have hSum := Finset.sum_nonneg (fun i hi =>
    mul_nonneg (ha i hi) (compensatedParity_quadratic_nonneg (y i) s u (hy i hi) hs))
  rw [hPacket] at hSum
  exact hSum

theorem finiteWeightedParity_signed_discriminant {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (s : Real) (hs : Or (s = 1) (s = -1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    (1 - 2 * momentRoundThreshold) ^ 2 *
        (Finset.sum S (fun i => a i * y i) -
          Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) ^ 2 <=
      4 * Finset.sum S (fun i => a i * y i) *
        (Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
          s * momentRoundThreshold *
            (Finset.sum S (fun i => a i * y i) -
              Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i)))) := by
  let M := Finset.sum S (fun i => a i * y i)
  let D := M - Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))
  let E := Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2)
  let u := s * (1 - 2 * momentRoundThreshold) * D / (2 * M)
  have hM : 0 < M := hMass
  have hQuad := finiteWeightedParity_quadratic S a y s u hs ha hy hMoment
  change 0 <= M * u ^ 2 - u * s * (1 - 2 * momentRoundThreshold) * D +
    E - s * momentRoundThreshold * D at hQuad
  have hSquare : (s * (1 - 2 * momentRoundThreshold) * D) ^ 2 =
      (1 - 2 * momentRoundThreshold) ^ 2 * D ^ 2 := by
    rcases hs with hS | hS
    case inl => rw [hS]; ring
    case inr => rw [hS]; ring
  have hAlgebra :
      4 * M * (M * u ^ 2 - u * s * (1 - 2 * momentRoundThreshold) * D +
        E - s * momentRoundThreshold * D) =
      4 * M * (E - s * momentRoundThreshold * D) -
        (1 - 2 * momentRoundThreshold) ^ 2 * D ^ 2 := by
    calc
      _ = 4 * M * (E - s * momentRoundThreshold * D) -
          (s * (1 - 2 * momentRoundThreshold) * D) ^ 2 := by
        dsimp only [u]
        field_simp [hM.ne']
        ring
      _ = _ := by rw [hSquare]
  have hNonneg := mul_nonneg (show 0 <= 4 * M by linarith) hQuad
  change (1 - 2 * momentRoundThreshold) ^ 2 * D ^ 2 <=
    4 * M * (E - s * momentRoundThreshold * D)
  nlinarith only [hAlgebra, hNonneg]

theorem finiteWeightedParity_stability {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    (1 - 2 * momentRoundThreshold) ^ 2 *
        (Finset.sum S (fun i => a i * y i) -
          Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) ^ 2 <=
      4 * Finset.sum S (fun i => a i * y i) *
        (Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
          momentRoundThreshold * abs
            (Finset.sum S (fun i => a i * y i) -
              Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i)))) := by
  by_cases hD : 0 <= Finset.sum S (fun i => a i * y i) -
      Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))
  case pos =>
    rw [abs_of_nonneg hD]
    simpa only [one_mul] using
      finiteWeightedParity_signed_discriminant S a y 1 (Or.inl rfl) ha hy hMoment hMass
  case neg =>
    rw [abs_of_neg (lt_of_not_ge hD)]
    have hSigned := finiteWeightedParity_signed_discriminant S a y (-1)
      (Or.inr rfl) ha hy hMoment hMass
    nlinarith only [hSigned]

theorem finiteWeightedParity_stability_cost {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    compensatedParityStabilityCost (Finset.sum S (fun i => a i * y i))
      (Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) <=
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  have hCross := finiteWeightedParity_stability S a y ha hy hMoment hMass
  have hDen : 0 < 4 * Finset.sum S (fun i => a i * y i) := by linarith
  have hCancel :
      ((1 - 2 * momentRoundThreshold) ^ 2 *
        (Finset.sum S (fun i => a i * y i) -
          Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) ^ 2 /
          (4 * Finset.sum S (fun i => a i * y i))) *
        (4 * Finset.sum S (fun i => a i * y i)) =
      (1 - 2 * momentRoundThreshold) ^ 2 *
        (Finset.sum S (fun i => a i * y i) -
          Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) ^ 2 := by
    field_simp [hMass.ne']
  unfold compensatedParityStabilityCost
  by_contra hNot
  have hBad := lt_of_not_ge hNot
  have hScaled := _root_.mul_lt_mul_of_pos_left hBad hDen
  nlinarith only [hCross, hCancel, hScaled]

theorem compensatedParityStabilityCost_unit_gap (mass discrepancy : Real)
    (hMass : 0 < mass) (hGap : 1 <= abs discrepancy) :
    momentRoundThreshold + (1 - 2 * momentRoundThreshold) ^ 2 / (4 * mass) <=
      compensatedParityStabilityCost mass discrepancy := by
  have hSquare : 1 <= discrepancy ^ 2 := by nlinarith [sq_abs discrepancy]
  have hCoeff : 0 <= (1 - 2 * momentRoundThreshold) ^ 2 / (4 * mass) :=
    div_nonneg (sq_nonneg _) (by linarith)
  have hCorrection := mul_nonneg hCoeff (sub_nonneg.mpr hSquare)
  have hLinear := mul_nonneg (le_of_lt momentRoundThreshold_bounds.1)
    (sub_nonneg.mpr hGap)
  have hIdentity :
      (1 - 2 * momentRoundThreshold) ^ 2 * discrepancy ^ 2 / (4 * mass) -
        (1 - 2 * momentRoundThreshold) ^ 2 / (4 * mass) =
      ((1 - 2 * momentRoundThreshold) ^ 2 / (4 * mass)) * (discrepancy ^ 2 - 1) := by ring
  unfold compensatedParityStabilityCost
  nlinarith only [hIdentity, hCorrection, hLinear]

theorem finiteWeightedParity_stability_scaled {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> 0 <= x i)
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i)) :
    compensatedParityStabilityCost (Finset.sum S (fun i => a i * x i) / t)
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
  have hCost := finiteWeightedParity_stability_cost S a (fun i => x i / t)
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

theorem threeLineWeightedParityStability_charge {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i)) :
    threeLineCharge * Finset.sum S a +
      threeLineSizeBiasedProfile t * Finset.sum S (fun i => a i * x i) +
      threeLineParityCubicCoefficient * t ^ 3 *
        compensatedParityStabilityCost (Finset.sum S (fun i => a i * x i) / t)
          (Finset.sum S (fun i => a i * x i) / t -
            Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t))) <=
      Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) := by
  have hCost := finiteWeightedParity_stability_scaled S a x t ht ha
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


theorem finiteWeightedParity_stability_gamma {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    (momentRoundThreshold - 1 / 4) *
        (Finset.sum S (fun i => a i * y i) -
          Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) ^ 2 <=
      Finset.sum S (fun i => a i * y i) *
        (Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
          momentRoundThreshold * abs
            (Finset.sum S (fun i => a i * y i) -
              Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i)))) := by
  have hCross := finiteWeightedParity_stability S a y ha hy hMoment hMass
  have hCoeff : (1 - 2 * momentRoundThreshold) ^ 2 =
      4 * (momentRoundThreshold - 1 / 4) := by
    nlinarith only [momentRoundThreshold_equation]
  rw [hCoeff] at hCross
  nlinarith only [hCross]

theorem compensatedParityStabilityCost_formula (mass discrepancy : Real) :
    compensatedParityStabilityCost mass discrepancy =
      momentRoundThreshold * abs discrepancy +
        (momentRoundThreshold - 1 / 4) * discrepancy ^ 2 / mass := by
  have hCoeff : (1 - 2 * momentRoundThreshold) ^ 2 =
      4 * (momentRoundThreshold - 1 / 4) := by
    nlinarith only [momentRoundThreshold_equation]
  unfold compensatedParityStabilityCost
  rw [hCoeff]
  by_cases hMass : mass = 0
  case pos => subst mass; simp
  case neg =>
    field_simp [hMass]

theorem compensatedParityStabilityCost_unit_budget (mass budget discrepancy : Real)
    (hMass : 0 < mass) (hBudget : mass <= budget) (hGap : 1 <= abs discrepancy) :
    momentRoundThreshold + (momentRoundThreshold - 1 / 4) / budget <=
      compensatedParityStabilityCost mass discrepancy := by
  have hBudgetPos : 0 < budget := lt_of_lt_of_le hMass hBudget
  have hGamma : 0 < momentRoundThreshold - 1 / 4 :=
    sub_pos.mpr momentRoundThreshold_gt_quarter
  have hRatio : 0 <= (momentRoundThreshold - 1 / 4) / budget :=
    div_nonneg (le_of_lt hGamma) (le_of_lt hBudgetPos)
  have hCancelB : ((momentRoundThreshold - 1 / 4) / budget) * budget =
      momentRoundThreshold - 1 / 4 := by field_simp [hBudgetPos.ne']
  have hCancelM : ((momentRoundThreshold - 1 / 4) / mass) * mass =
      momentRoundThreshold - 1 / 4 := by field_simp [hMass.ne']
  have hScaled := _root_.mul_le_mul_of_nonneg_left hBudget hRatio
  have hCompare : (momentRoundThreshold - 1 / 4) / budget <=
      (momentRoundThreshold - 1 / 4) / mass := by
    by_contra hNot
    have hBad := lt_of_not_ge hNot
    have hProduct := _root_.mul_lt_mul_of_pos_right hBad hMass
    nlinarith only [hProduct, hCancelB, hCancelM, hScaled]
  have hUnit := compensatedParityStabilityCost_unit_gap mass discrepancy hMass hGap
  have hFormula := compensatedParityStabilityCost_formula mass 1
  simp only [compensatedParityStabilityCost, abs_one, one_pow, mul_one] at hFormula
  rw [hFormula] at hUnit
  linarith

theorem compensatedParityStability_budget_strict (budget : Real) (hBudget : 0 < budget) :
    momentRoundThreshold <
      momentRoundThreshold + (momentRoundThreshold - 1 / 4) / budget := by
  have hPositive := div_pos (sub_pos.mpr momentRoundThreshold_gt_quarter) hBudget
  linarith


theorem threeLineKernelParityCoefficient_continuousAt_zero :
    ContinuousAt threeLineKernelParityCoefficient 0 := by
  unfold threeLineKernelParityCoefficient threeLineSizeBiasedRemainder
  fun_prop (disch := norm_num [threeLineRadius1, threeLineRadius2, threeLineRadius3])

theorem threeLineKernelParityCoefficient_zero :
    threeLineKernelParityCoefficient 0 =
      momentRoundThreshold * threeLineParityCubicCoefficient := by
  unfold threeLineKernelParityCoefficient
  simp only [zero_mul, threeLineSizeBiasedRemainder_origin]

theorem parityStability_stronger_near_zero (budget : Real) (hBudget : 0 < budget) :
    exists radius : Real, And (0 < radius) (forall t : Real, 0 < t -> t < radius ->
      threeLineKernelParityCoefficient t <
        threeLineParityCubicCoefficient *
          (momentRoundThreshold + (momentRoundThreshold - 1 / 4) / budget)) := by
  have hTau := threeLineParityCubicCoefficient_pos
  have hGap : 0 < threeLineParityCubicCoefficient *
      ((momentRoundThreshold - 1 / 4) / budget) :=
    mul_pos hTau (div_pos (sub_pos.mpr momentRoundThreshold_gt_quarter) hBudget)
  choose radius hRadius hClose using
    (Metric.continuousAt_iff.mp threeLineKernelParityCoefficient_continuousAt_zero)
      (threeLineParityCubicCoefficient * ((momentRoundThreshold - 1 / 4) / budget)) hGap
  apply Exists.intro radius
  apply And.intro hRadius
  intro t ht htSmall
  have hDist : dist t 0 < radius := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    exact htSmall
  have hNear := hClose hDist
  rw [threeLineKernelParityCoefficient_zero, Real.dist_eq] at hNear
  have hUpper := (abs_lt.mp hNear).2
  nlinarith only [hUpper]

end PrimeFactorOscillations
