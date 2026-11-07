/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CompensatedMomentParityStability

/-! # Sharp one-sided stability of the compensated parity bound

The second-moment carrier retains the sign of transport below one.
Sharpness statements concern real nonnegative weights, not actual zeros.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def sharpParityCarrier : Real := 2 * (1 - momentRoundThreshold)

def sharpParityCoefficient : Real := 1 - 3 * momentRoundThreshold

def sharpParityStabilityCost (mass discrepancy : Real) : Real :=
  momentRoundThreshold * abs discrepancy +
    sharpParityCoefficient * discrepancy ^ 2 / mass

theorem sharpParityCarrier_pos : 0 < sharpParityCarrier := by
  unfold sharpParityCarrier
  have hd := momentRoundThreshold_lt_three_tenths
  linarith

theorem sharpParityCoefficient_pos : 0 < sharpParityCoefficient := by
  unfold sharpParityCoefficient
  have hd := momentRoundThreshold_lt_three_tenths
  linarith

theorem sharpParityCoefficient_identity :
    (1 - 2 * momentRoundThreshold) ^ 2 =
      sharpParityCarrier * sharpParityCoefficient := by
  unfold sharpParityCarrier sharpParityCoefficient
  nlinarith only [momentRoundThreshold_equation]

theorem compensatedParityTransport_nonpos_below_one (d s y : Real)
    (hd : And (1 / 4 <= d) (d < 1 / 2))
    (hRoot : 2 * d ^ 2 - 4 * d + 1 = 0)
    (hy : And (0 <= y) (y <= 1)) (hs : Or (s = 1) (s = -1)) :
    compensatedParityTransport d s y <= 0 := by
  classical
  have hd0 : 0 <= d := by linarith
  rcases hs with hs | hs
  case inl =>
    subst s
    by_cases hdy : d <= y
    case pos =>
      have hk : compensatedParityTransport d 1 y =
          (2 * d * y + 1 - 2 * d) * (y - 1) := by
        unfold compensatedParityTransport momentRoundIndicator
        rw [ite_eq_left hdy]
        ring
      rw [hk]
      exact mul_nonpos_of_nonneg_of_nonpos
        (by nlinarith only [mul_nonneg hd0 hy.1, hd.2]) (by linarith)
    case neg =>
      have hly : y < d := lt_of_not_ge hdy
      have hk : compensatedParityTransport d 1 y = 2 * d * y * (y - d) := by
        unfold compensatedParityTransport momentRoundIndicator
        rw [ite_eq_right hdy]
        nlinarith only [hRoot, congrArg (fun v : Real => v * y) hRoot]
      rw [hk]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) hy.1) (by linarith)
  case inr =>
    subst s
    by_cases hdy : d <= y
    case pos =>
      have hk : compensatedParityTransport d (-1) y =
          (2 - 2 * d) * (y - d) * (y - 1) := by
        unfold compensatedParityTransport momentRoundIndicator
        rw [ite_eq_left hdy]
        nlinarith only [hRoot, congrArg (fun v : Real => v * y) hRoot]
      rw [hk]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by linarith) (sub_nonneg.mpr hdy)) (by linarith)
    case neg =>
      have hly : y < d := lt_of_not_ge hdy
      have hk : compensatedParityTransport d (-1) y =
          y * ((2 - 2 * d) * y + 4 * d - 3) := by
        unfold compensatedParityTransport momentRoundIndicator
        rw [ite_eq_right hdy]
        ring
      rw [hk]
      have hMul := mul_nonneg (show 0 <= 2 - 2 * d by linarith)
        (show 0 <= d - y by linarith)
      exact mul_nonpos_of_nonneg_of_nonpos hy.1 (by nlinarith only [hRoot, hMul, hd.2])

theorem compensatedParity_positive_second_moment (d y : Real)
    (hd : And (1 / 4 <= d) (d < 1 / 2)) (hy : 1 <= y) :
    compensatedParityTransport d 1 y ^ 2 <=
      (2 - 2 * d) * y ^ 2 * compensatedParityResidual d 1 y := by
  classical
  have hd0 : 0 <= d := by linarith
  have hdy : d <= y := by linarith
  have hP0 : 0 <= 2 * d * y + 1 - 2 * d := by
    nlinarith only [mul_nonneg hd0 (show 0 <= y by linarith), hd.2]
  have hP1 : 2 * d * y + 1 - 2 * d <= y := by
    nlinarith only [mul_nonneg (show 0 <= 1 - 2 * d by linarith)
      (show 0 <= y - 1 by linarith)]
  have hSq : (2 * d * y + 1 - 2 * d) ^ 2 <= y ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hP1)
      (show 0 <= y + (2 * d * y + 1 - 2 * d) by linarith)]
  have hFactor : 1 <= (2 - 2 * d) * (y + d) := by
    have hProduct := mul_nonneg (show 0 <= 2 - 2 * d by linarith)
      (show 0 <= y + d - 1 by linarith)
    nlinarith only [hProduct, hd.2]
  have hQuad : (2 * d * y + 1 - 2 * d) ^ 2 <=
      (2 - 2 * d) * y ^ 2 * (y + d) := by
    nlinarith only [hSq, mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hFactor)]
  have hScaled := _root_.mul_le_mul_of_nonneg_right hQuad (sq_nonneg (y - 1))
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

theorem compensatedParity_negative_second_moment (d y : Real)
    (hd : And (1 / 4 <= d) (d < 1 / 2))
    (hRoot : 2 * d ^ 2 - 4 * d + 1 = 0) (hy : 1 <= y) :
    compensatedParityTransport d (-1) y ^ 2 <=
      (2 - 2 * d) * y ^ 2 * compensatedParityResidual d (-1) y := by
  classical
  have hdy : d <= y := by linarith
  have hR : compensatedParityResidual d (-1) y = (y - d) * (y - 1) ^ 2 := by
    unfold compensatedParityResidual momentRoundIndicator
    rw [ite_eq_left hdy]
    ring
  have hK : compensatedParityTransport d (-1) y =
      (2 - 2 * d) * (y - d) * (y - 1) := by
    unfold compensatedParityTransport momentRoundIndicator
    rw [ite_eq_left hdy]
    nlinarith only [hRoot, congrArg (fun v : Real => v * y) hRoot]
  have hDiff : y ^ 2 - (2 - 2 * d) * (y - d) =
      (y - 1) * (y - (1 - 2 * d)) := by nlinarith only [hRoot]
  have hBase : 0 <= y ^ 2 - (2 - 2 * d) * (y - d) := by
    rw [hDiff]
    exact mul_nonneg (by linarith) (by linarith)
  have hProduct := mul_nonneg
    (mul_nonneg (mul_nonneg (show 0 <= 2 - 2 * d by linarith)
      (sub_nonneg.mpr hdy)) (sq_nonneg (y - 1))) hBase
  rw [hR, hK]
  nlinarith only [hProduct]

theorem compensatedParity_one_sided_quadratic (y s u : Real)
    (hy : 0 <= y) (hs : Or (s = 1) (s = -1)) (hu : 0 <= u) :
    0 <= (sharpParityCarrier / 4) * y ^ 2 * u ^ 2 -
      u * compensatedParityTransport momentRoundThreshold s y +
      compensatedParityResidual momentRoundThreshold s y := by
  have hd : And (1 / 4 <= momentRoundThreshold) (momentRoundThreshold < 1 / 2) :=
    And.intro momentRoundThreshold_gt_quarter.le momentRoundThreshold_bounds.2
  have hC := sharpParityCarrier_pos
  by_cases hLow : y <= 1
  case pos =>
    have hK := compensatedParityTransport_nonpos_below_one momentRoundThreshold s y
      hd momentRoundThreshold_equation (And.intro hy hLow) hs
    have hR : 0 <= compensatedParityResidual momentRoundThreshold s y := by
      simpa using compensatedParity_quadratic_nonneg y s 0 hy hs
    have hFirst : 0 <= (sharpParityCarrier / 4) * y ^ 2 * u ^ 2 := by positivity
    nlinarith only [hFirst, hR, mul_nonpos_of_nonneg_of_nonpos hu hK]
  case neg =>
    have hHigh : 1 <= y := le_of_lt (lt_of_not_ge hLow)
    have hCertificate :
        compensatedParityTransport momentRoundThreshold s y ^ 2 <=
          sharpParityCarrier * y ^ 2 * compensatedParityResidual momentRoundThreshold s y := by
      rcases hs with hs | hs
      case inl =>
        rw [hs]
        have hc := compensatedParity_positive_second_moment momentRoundThreshold y hd hHigh
        unfold sharpParityCarrier
        nlinarith only [hc]
      case inr =>
        rw [hs]
        have hc := compensatedParity_negative_second_moment momentRoundThreshold y hd
          momentRoundThreshold_equation hHigh
        unfold sharpParityCarrier
        nlinarith only [hc]
    have hSquare := sq_nonneg
      ((sharpParityCarrier / 2) * y ^ 2 * u - compensatedParityTransport momentRoundThreshold s y)
    have hProduct : 0 <= sharpParityCarrier * y ^ 2 *
        ((sharpParityCarrier / 4) * y ^ 2 * u ^ 2 -
          u * compensatedParityTransport momentRoundThreshold s y +
          compensatedParityResidual momentRoundThreshold s y) := by
      nlinarith only [hCertificate, hSquare]
    have hPositive : 0 < sharpParityCarrier * y ^ 2 := mul_pos hC (by nlinarith only [hHigh])
    exact nonneg_of_mul_nonneg_right hProduct hPositive

theorem finiteWeightedParity_one_sided_quadratic {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (s u : Real) (hs : Or (s = 1) (s = -1)) (hu : 0 <= u)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i)) :
    0 <= (sharpParityCarrier / 4) * Finset.sum S (fun i => a i * y i) * u ^ 2 -
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
      Finset.sum S (fun i => a i * ((sharpParityCarrier / 4) * (y i) ^ 2 * u ^ 2 -
        u * compensatedParityTransport momentRoundThreshold s (y i) +
        compensatedParityResidual momentRoundThreshold s (y i))) =
      (sharpParityCarrier / 4) * Finset.sum S (fun i => a i * y i) * u ^ 2 -
        u * s * (1 - 2 * momentRoundThreshold) *
          (Finset.sum S (fun i => a i * y i) -
            Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) +
        Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
        s * momentRoundThreshold *
          (Finset.sum S (fun i => a i * y i) -
            Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) := by
    calc
      _ = Finset.sum S (fun i =>
          (((sharpParityCarrier / 4) * (a i * (y i) ^ 2)) * u ^ 2 - u * (a i * y i * (y i - 1))) -
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
          <- Finset.mul_sum, hG, hH, mul_zero, sub_zero]
        have hc : Finset.sum S (fun i =>
            (sharpParityCarrier / 4) * (a i * (y i) ^ 2) * u ^ 2) =
            (sharpParityCarrier / 4) * Finset.sum S (fun i => a i * y i) * u ^ 2 := by
          calc
            _ = Finset.sum S (fun i => ((sharpParityCarrier / 4) * u ^ 2) *
                (a i * (y i) ^ 2)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
            _ = ((sharpParityCarrier / 4) * u ^ 2) *
                Finset.sum S (fun i => a i * (y i) ^ 2) := by rw [Finset.mul_sum]
            _ = _ := by rw [hMoment]; ring
        rw [hc]
  have hSum := Finset.sum_nonneg (fun i hi =>
    mul_nonneg (ha i hi) (compensatedParity_one_sided_quadratic (y i) s u (hy i hi) hs hu))
  rw [hPacket] at hSum
  exact hSum


theorem finiteWeightedParity_sharp_stability {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    sharpParityStabilityCost (Finset.sum S (fun i => a i * y i))
      (Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) <=
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  classical
  let M := Finset.sum S (fun i => a i * y i)
  let D := M - Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))
  let E := Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2)
  let s : Real := if 0 <= D then 1 else -1
  let u := 2 * (1 - 2 * momentRoundThreshold) * abs D / (sharpParityCarrier * M)
  have hM : 0 < M := hMass
  have hC := sharpParityCarrier_pos
  have hs : Or (s = 1) (s = -1) := by
    by_cases h : 0 <= D
    case pos => exact Or.inl (by simp [s, h])
    case neg => exact Or.inr (by simp [s, h])
  have hsD : s * D = abs D := by
    by_cases h : 0 <= D
    case pos => simp [s, h, abs_of_nonneg h]
    case neg => simp [s, h, abs_of_neg (lt_of_not_ge h)]
  have hu : 0 <= u := by
    dsimp only [u]
    exact div_nonneg (mul_nonneg (by
      have hd := momentRoundThreshold_bounds.2
      linarith) (abs_nonneg D)) (mul_nonneg hC.le hM.le)
  have hQuad := finiteWeightedParity_one_sided_quadratic S a y s u hs hu ha hy hMoment
  change 0 <= (sharpParityCarrier / 4) * M * u ^ 2 -
    u * s * (1 - 2 * momentRoundThreshold) * D + E -
      s * momentRoundThreshold * D at hQuad
  have hLinear : s * (1 - 2 * momentRoundThreshold) * D =
      (1 - 2 * momentRoundThreshold) * abs D := by
    calc
      _ = (1 - 2 * momentRoundThreshold) * (s * D) := by ring
      _ = _ := by rw [hsD]
  have hRound : s * momentRoundThreshold * D = momentRoundThreshold * abs D := by
    calc
      _ = momentRoundThreshold * (s * D) := by ring
      _ = _ := by rw [hsD]
  have hQuad' : 0 <= (sharpParityCarrier / 4) * M * u ^ 2 -
      u * ((1 - 2 * momentRoundThreshold) * abs D) + E -
        momentRoundThreshold * abs D := by
    have hLinearU : u * s * (1 - 2 * momentRoundThreshold) * D =
        u * ((1 - 2 * momentRoundThreshold) * abs D) := by
      calc
        _ = u * (s * (1 - 2 * momentRoundThreshold) * D) := by ring
        _ = _ := by rw [hLinear]
    rw [hLinearU, hRound] at hQuad
    exact hQuad
  have hAlgebra :
      sharpParityCarrier * M * ((sharpParityCarrier / 4) * M * u ^ 2 -
        u * ((1 - 2 * momentRoundThreshold) * abs D) + E -
        momentRoundThreshold * abs D) =
      sharpParityCarrier * M * (E - momentRoundThreshold * abs D) -
        (1 - 2 * momentRoundThreshold) ^ 2 * D ^ 2 := by
    calc
      _ = sharpParityCarrier * M * (E - momentRoundThreshold * abs D) -
          (1 - 2 * momentRoundThreshold) ^ 2 * (abs D) ^ 2 := by
        dsimp only [u]
        field_simp [hC.ne', hM.ne']
        ring
      _ = _ := by rw [sq_abs]
  have hNonneg := mul_nonneg (mul_nonneg hC.le hM.le) hQuad'
  rw [hAlgebra, sharpParityCoefficient_identity] at hNonneg
  have hScaled : sharpParityCoefficient * D ^ 2 <= M * (E - momentRoundThreshold * abs D) := by
    by_contra hn
    have hp := mul_pos hC (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hNonneg, hp]
  have hDiv : sharpParityCoefficient * D ^ 2 / M <= E - momentRoundThreshold * abs D := by
    have he : (sharpParityCoefficient * D ^ 2 / M) * M = sharpParityCoefficient * D ^ 2 := by
      field_simp [hM.ne']
    by_contra hn
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hM
    nlinarith only [he, hp, hScaled]
  change momentRoundThreshold * abs D + sharpParityCoefficient * D ^ 2 / M <= E
  linarith

theorem finiteWeightedParity_sharp_stability_scaled {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> 0 <= x i)
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i)) :
    sharpParityStabilityCost (Finset.sum S (fun i => a i * x i) / t)
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
  have hCost := finiteWeightedParity_sharp_stability S a (fun i => x i / t)
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

theorem threeLineWeightedSharpParityStability_charge {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i)) :
    threeLineCharge * Finset.sum S a +
      threeLineSizeBiasedProfile t * Finset.sum S (fun i => a i * x i) +
      threeLineParityCubicCoefficient * t ^ 3 *
        sharpParityStabilityCost (Finset.sum S (fun i => a i * x i) / t)
          (Finset.sum S (fun i => a i * x i) / t -
            Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t))) <=
      Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) := by
  have hCost := finiteWeightedParity_sharp_stability_scaled S a x t ht ha
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



theorem sharpParityCoefficient_improves :
    momentRoundThreshold - 1 / 4 < sharpParityCoefficient := by
  unfold sharpParityCoefficient
  have hd := momentRoundThreshold_lt_three_tenths
  linarith

theorem sharpParityCoefficient_gain :
    sharpParityCoefficient =
      2 * sharpParityCarrier * (momentRoundThreshold - 1 / 4) := by
  unfold sharpParityCoefficient sharpParityCarrier
  nlinarith only [momentRoundThreshold_equation]

def sharpParityModelWeight (z : Real) : Real :=
  2 * z * (z - 1) / (1 - 2 * momentRoundThreshold)

def sharpParityModelMass (z : Real) : Real :=
  sharpParityModelWeight z * momentRoundThreshold + z

def sharpParityModelDiscrepancy (z : Real) : Real :=
  sharpParityModelMass z - (sharpParityModelWeight z + 1)

def sharpParityModelEnergy (z : Real) : Real :=
  sharpParityModelWeight z * momentRoundThreshold * (momentRoundThreshold - 1) ^ 2 +
    z * (z - 1) ^ 2

theorem sharpParityModelWeight_pos (z : Real) (hz : 1 < z) :
    0 < sharpParityModelWeight z := by
  unfold sharpParityModelWeight
  have hd := momentRoundThreshold_bounds.2
  exact div_pos (mul_pos (by linarith) (sub_pos.mpr hz)) (by linarith)

theorem sharpParityModel_moment (z : Real) :
    sharpParityModelWeight z * momentRoundThreshold ^ 2 + z ^ 2 =
      sharpParityModelWeight z * momentRoundThreshold + z := by
  have hA : 0 < 1 - 2 * momentRoundThreshold := by
    have hd := momentRoundThreshold_bounds.2
    linarith
  have hR : 2 * momentRoundThreshold * (1 - momentRoundThreshold) /
      (1 - 2 * momentRoundThreshold) = 1 := by
    field_simp [hA.ne']
    nlinarith only [momentRoundThreshold_equation]
  have hm : sharpParityModelWeight z * momentRoundThreshold * (1 - momentRoundThreshold) =
      z * (z - 1) := by
    calc
      _ = (2 * momentRoundThreshold * (1 - momentRoundThreshold) /
          (1 - 2 * momentRoundThreshold)) * z * (z - 1) := by
        unfold sharpParityModelWeight
        ring
      _ = _ := by rw [hR]; ring
  nlinarith only [hm]

theorem sharpParityModel_mass_formula (z : Real) :
    sharpParityModelMass z = z * (sharpParityCarrier * z - (1 - 2 * momentRoundThreshold)) := by
  have hA : 0 < 1 - 2 * momentRoundThreshold := by
    have hd := momentRoundThreshold_bounds.2
    linarith
  have hR : 2 * momentRoundThreshold / (1 - 2 * momentRoundThreshold) =
      sharpParityCarrier := by
    field_simp [hA.ne']
    unfold sharpParityCarrier
    nlinarith only [momentRoundThreshold_equation]
  unfold sharpParityModelMass
  calc
    _ = (2 * momentRoundThreshold / (1 - 2 * momentRoundThreshold)) * z * (z - 1) + z := by
      unfold sharpParityModelWeight
      ring
    _ = _ := by rw [hR]; unfold sharpParityCarrier; ring

theorem sharpParityModel_discrepancy_formula (z : Real) :
    sharpParityModelDiscrepancy z =
      -(z - 1) * ((sharpParityCarrier + 2) * z - 1) := by
  have hA : 0 < 1 - 2 * momentRoundThreshold := by
    have hd := momentRoundThreshold_bounds.2
    linarith
  have hR : 2 * (1 - momentRoundThreshold) / (1 - 2 * momentRoundThreshold) =
      sharpParityCarrier + 2 := by
    field_simp [hA.ne']
    unfold sharpParityCarrier
    nlinarith only [momentRoundThreshold_equation]
  unfold sharpParityModelDiscrepancy sharpParityModelMass
  calc
    _ = -(2 * (1 - momentRoundThreshold) / (1 - 2 * momentRoundThreshold)) * z * (z - 1) + z - 1 := by
      unfold sharpParityModelWeight
      ring
    _ = _ := by rw [hR]; ring

theorem sharpParityModel_discrepancy_neg (z : Real) (hz : 1 < z) :
    sharpParityModelDiscrepancy z < 0 := by
  rw [sharpParityModel_discrepancy_formula]
  have hC := sharpParityCarrier_pos
  have hp : 0 < (sharpParityCarrier + 2) * z - 1 := by
    nlinarith only [mul_pos hC (show 0 < z by linarith), hz]
  exact mul_neg_of_neg_of_pos (by linarith) hp

theorem sharpParityModel_energy_formula (z : Real) (hz : 1 < z) :
    sharpParityModelEnergy z - momentRoundThreshold * abs (sharpParityModelDiscrepancy z) =
      (z - momentRoundThreshold) * (z - 1) ^ 2 := by
  rw [abs_of_neg (sharpParityModel_discrepancy_neg z hz)]
  have hm := congrArg (fun v : Real => v * momentRoundThreshold) (sharpParityModel_moment z)
  unfold sharpParityModelEnergy sharpParityModelDiscrepancy sharpParityModelMass
  nlinarith only [hm]

theorem sharpParityModel_exact_ratio (z : Real) (hz : 1 < z) :
    sharpParityModelMass z *
      (sharpParityModelEnergy z - momentRoundThreshold * abs (sharpParityModelDiscrepancy z)) =
      sharpParityCoefficient * z * sharpParityModelDiscrepancy z ^ 2 := by
  have hCA : sharpParityCarrier * momentRoundThreshold = 1 - 2 * momentRoundThreshold := by
    unfold sharpParityCarrier
    nlinarith only [momentRoundThreshold_equation]
  have hAG : (1 - 2 * momentRoundThreshold) * momentRoundThreshold = sharpParityCoefficient := by
    unfold sharpParityCoefficient
    nlinarith only [momentRoundThreshold_equation]
  have hGC : sharpParityCoefficient * (sharpParityCarrier + 2) = 1 - 2 * momentRoundThreshold := by
    unfold sharpParityCoefficient sharpParityCarrier
    nlinarith only [momentRoundThreshold_equation]
  have hAC : (1 - 2 * momentRoundThreshold) * (sharpParityCarrier + 2) = sharpParityCarrier := by
    unfold sharpParityCarrier
    nlinarith only [momentRoundThreshold_equation]
  have hGC2 : sharpParityCoefficient * (sharpParityCarrier + 2) ^ 2 = sharpParityCarrier := by
    calc
      _ = (sharpParityCoefficient * (sharpParityCarrier + 2)) * (sharpParityCarrier + 2) := by ring
      _ = _ := by rw [hGC, hAC]
  have hf : (sharpParityCarrier * z - (1 - 2 * momentRoundThreshold)) * (z - momentRoundThreshold) =
      sharpParityCoefficient * ((sharpParityCarrier + 2) * z - 1) ^ 2 := by
    calc
      _ = sharpParityCarrier * z ^ 2 -
          (sharpParityCarrier * momentRoundThreshold + (1 - 2 * momentRoundThreshold)) * z +
          (1 - 2 * momentRoundThreshold) * momentRoundThreshold := by ring
      _ = sharpParityCarrier * z ^ 2 - 2 * (1 - 2 * momentRoundThreshold) * z +
          sharpParityCoefficient := by rw [hCA, hAG]; ring
      _ = _ := by
        nlinarith only [congrArg (fun v : Real => v * z ^ 2) hGC2,
          congrArg (fun v : Real => v * z) hGC]
  rw [sharpParityModel_mass_formula, sharpParityModel_energy_formula z hz,
    sharpParityModel_discrepancy_formula]
  calc
    _ = z * ((sharpParityCarrier * z - (1 - 2 * momentRoundThreshold)) *
          (z - momentRoundThreshold)) * (z - 1) ^ 2 := by ring
    _ = _ := by rw [hf]; ring

theorem sharpParityCoefficient_optimal (c : Real) (hc : sharpParityCoefficient < c) :
    exists z : Real, And (1 < z)
      (sharpParityModelEnergy z <
        momentRoundThreshold * abs (sharpParityModelDiscrepancy z) +
          c * sharpParityModelDiscrepancy z ^ 2 / sharpParityModelMass z) := by
  let z := (1 + c / sharpParityCoefficient) / 2
  have hG := sharpParityCoefficient_pos
  have hCancel : (c / sharpParityCoefficient) * sharpParityCoefficient = c := by
    field_simp [hG.ne']
  have hz : 1 < z := by
    dsimp only [z]
    by_contra hn
    have hp := mul_nonneg hG.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith only [hc, hCancel, hp]
  have hzc : sharpParityCoefficient * z < c := by
    dsimp only [z]
    nlinarith only [hc, hCancel]
  have hM : 0 < sharpParityModelMass z := by
    unfold sharpParityModelMass
    exact add_pos (mul_pos (sharpParityModelWeight_pos z hz) momentRoundThreshold_bounds.1)
      (by linarith)
  have hD := sharpParityModel_discrepancy_neg z hz
  have hD2 : 0 < sharpParityModelDiscrepancy z ^ 2 := sq_pos_of_neg hD
  have hExact := sharpParityModel_exact_ratio z hz
  have hStrict := mul_pos (sub_pos.mpr hzc) hD2
  have hCancelM : (c * sharpParityModelDiscrepancy z ^ 2 / sharpParityModelMass z) *
      sharpParityModelMass z = c * sharpParityModelDiscrepancy z ^ 2 := by field_simp [hM.ne']
  refine Exists.intro z (And.intro hz ?_)
  by_contra hn
  have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) hM.le
  nlinarith only [hExact, hStrict, hCancelM, hp]

end PrimeFactorOscillations
