/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.SharpCompensatedParityStability

/-! # Rigidity of sharp compensated parity stability -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations


theorem compensatedParity_high_square_strict (d s y : Real)
    (hd : And (1 / 4 <= d) (d < 1 / 2))
    (hRoot : 2 * d ^ 2 - 4 * d + 1 = 0)
    (hy : 1 < y) (hs : Or (s = 1) (s = -1)) :
    compensatedParityTransport d s y ^ 2 <
      (2 - 2 * d) * y ^ 2 * compensatedParityResidual d s y := by
  classical
  have hdy : d <= y := by linarith
  have hd0 : 0 <= d := by linarith
  rcases hs with hs | hs
  case inl =>
    subst s
    have hp0 : 0 <= 2 * d * y + 1 - 2 * d := by
      nlinarith only [mul_nonneg hd0 (show 0 <= y by linarith), hd.2]
    have hp1 : 2 * d * y + 1 - 2 * d <= y := by
      nlinarith only [mul_nonneg (show 0 <= 1 - 2 * d by linarith)
        (show 0 <= y - 1 by linarith)]
    have hpSq : (2 * d * y + 1 - 2 * d) ^ 2 <= y ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hp1)
        (show 0 <= y + (2 * d * y + 1 - 2 * d) by linarith)]
    have hf : 1 < (2 - 2 * d) * (y + d) := by
      have hm := mul_nonneg (show 0 <= 2 - 2 * d by linarith)
        (show 0 <= y + d - 1 by linarith)
      nlinarith only [hm, hd.2]
    have hq : (2 * d * y + 1 - 2 * d) ^ 2 <
        (2 - 2 * d) * y ^ 2 * (y + d) := by
      have hm := mul_pos (show 0 < y ^ 2 by positivity) (sub_pos.mpr hf)
      nlinarith only [hm, hpSq]
    have hScaled := _root_.mul_lt_mul_of_pos_right hq (sq_pos_of_pos (sub_pos.mpr hy))
    have hR : compensatedParityResidual d 1 y = (y + d) * (y - 1) ^ 2 := by
      unfold compensatedParityResidual momentRoundIndicator
      rw [ite_eq_left hdy]
      ring
    have hK : compensatedParityTransport d 1 y = (2 * d * y + 1 - 2 * d) * (y - 1) := by
      unfold compensatedParityTransport momentRoundIndicator
      rw [ite_eq_left hdy]
      ring
    rw [hR, hK]
    nlinarith only [hScaled]
  case inr =>
    subst s
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
    have hBase : 0 < y ^ 2 - (2 - 2 * d) * (y - d) := by
      rw [hDiff]
      exact mul_pos (sub_pos.mpr hy) (by linarith)
    have hProduct := mul_pos
      (mul_pos (mul_pos (show 0 < 2 - 2 * d by linarith)
        (show 0 < y - d by linarith)) (sq_pos_of_pos (sub_pos.mpr hy))) hBase
    rw [hR, hK]
    nlinarith only [hProduct]

theorem compensatedParity_one_sided_quadratic_pos (y s u : Real)
    (hy : 0 < y) (hs : Or (s = 1) (s = -1)) (hu : 0 < u) :
    0 < (sharpParityCarrier / 4) * y ^ 2 * u ^ 2 -
      u * compensatedParityTransport momentRoundThreshold s y +
      compensatedParityResidual momentRoundThreshold s y := by
  have hd : And (1 / 4 <= momentRoundThreshold) (momentRoundThreshold < 1 / 2) :=
    And.intro momentRoundThreshold_gt_quarter.le momentRoundThreshold_bounds.2
  have hC := sharpParityCarrier_pos
  by_cases hLow : y <= 1
  case pos =>
    have hK := compensatedParityTransport_nonpos_below_one momentRoundThreshold s y
      hd momentRoundThreshold_equation (And.intro hy.le hLow) hs
    have hR : 0 <= compensatedParityResidual momentRoundThreshold s y := by
      simpa using compensatedParity_quadratic_nonneg y s 0 hy.le hs
    have hFirst : 0 < (sharpParityCarrier / 4) * y ^ 2 * u ^ 2 := by positivity
    nlinarith only [hFirst, hR, mul_nonpos_of_nonneg_of_nonpos hu.le hK]
  case neg =>
    have hHigh : 1 < y := lt_of_not_ge hLow
    have hc := compensatedParity_high_square_strict momentRoundThreshold s y hd
      momentRoundThreshold_equation hHigh hs
    have hCertificate :
        compensatedParityTransport momentRoundThreshold s y ^ 2 <
          sharpParityCarrier * y ^ 2 * compensatedParityResidual momentRoundThreshold s y := by
      unfold sharpParityCarrier
      nlinarith only [hc]
    have hSquare := sq_nonneg
      ((sharpParityCarrier / 2) * y ^ 2 * u - compensatedParityTransport momentRoundThreshold s y)
    have hProduct : 0 < sharpParityCarrier * y ^ 2 *
        ((sharpParityCarrier / 4) * y ^ 2 * u ^ 2 -
          u * compensatedParityTransport momentRoundThreshold s y +
          compensatedParityResidual momentRoundThreshold s y) := by
      nlinarith only [hCertificate, hSquare]
    by_contra hn
    have hNonpos := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hC.le (sq_nonneg y)) (le_of_not_gt hn)
    linarith only [hProduct, hNonpos]

theorem finiteWeightedParity_one_sided_quadratic_strict {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (s u : Real) (hs : Or (s = 1) (s = -1)) (hu : 0 < u)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    0 < (sharpParityCarrier / 4) * Finset.sum S (fun i => a i * y i) * u ^ 2 -
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
  have hEach : forall i, Membership.mem S i -> 0 <= a i *
      ((sharpParityCarrier / 4) * (y i) ^ 2 * u ^ 2 -
        u * compensatedParityTransport momentRoundThreshold s (y i) +
        compensatedParityResidual momentRoundThreshold s (y i)) :=
    fun i hi => mul_nonneg (ha i hi)
      (compensatedParity_one_sided_quadratic (y i) s u (hy i hi) hs hu.le)
  have hw : exists i, And (Membership.mem S i) (0 < a i * y i) := by
    by_contra hn
    have hNonpos : Finset.sum S (fun i => a i * y i) <= 0 :=
      Finset.sum_nonpos (fun i hi => le_of_not_gt (fun hp =>
        hn (Exists.intro i (And.intro hi hp))))
    linarith only [hMass, hNonpos]
  choose i hi using hw
  have haPos : 0 < a i := by
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (hy i hi.1)
    linarith only [hm, hi.2]
  have hyPos : 0 < y i := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (ha i hi.1) (le_of_not_gt hn)
    linarith only [hm, hi.2]
  have hTerm := mul_pos haPos (compensatedParity_one_sided_quadratic_pos (y i) s u hyPos hs hu)
  have hSum := Finset.sum_pos' hEach (Exists.intro i (And.intro hi.1 hTerm))
  rw [hPacket] at hSum
  exact hSum

theorem finiteWeightedParity_sharp_stability_strict {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hDiscrepancy : Not ((Finset.sum S (fun i => a i * y i) -
      Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) = 0)) :
    sharpParityStabilityCost (Finset.sum S (fun i => a i * y i))
      (Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) <
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
  have hu : 0 < u := by
    dsimp only [u]
    exact div_pos (mul_pos (by
      have hd := momentRoundThreshold_bounds.2
      linarith) (abs_pos.mpr hDiscrepancy)) (mul_pos hC hM)
  have hQuad := finiteWeightedParity_one_sided_quadratic_strict S a y s u hs hu ha hy hMoment hMass
  change 0 < (sharpParityCarrier / 4) * M * u ^ 2 -
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
  have hQuad' : 0 < (sharpParityCarrier / 4) * M * u ^ 2 -
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
  have hNonneg := mul_pos (mul_pos hC hM) hQuad'
  rw [hAlgebra, sharpParityCoefficient_identity] at hNonneg
  have hScaled : sharpParityCoefficient * D ^ 2 < M * (E - momentRoundThreshold * abs D) := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos hC.le
      (sub_nonpos.mpr (le_of_not_gt hn))
    nlinarith only [hNonneg, hp]
  have hDiv : sharpParityCoefficient * D ^ 2 / M < E - momentRoundThreshold * abs D := by
    have he : (sharpParityCoefficient * D ^ 2 / M) * M = sharpParityCoefficient * D ^ 2 := by
      field_simp [hM.ne']
    by_contra hn
    have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hn)) hM.le
    nlinarith only [he, hp, hScaled]
  change momentRoundThreshold * abs D + sharpParityCoefficient * D ^ 2 / M < E
  linarith


theorem finiteWeightedParity_sharp_equality_iff {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    (sharpParityStabilityCost (Finset.sum S (fun i => a i * y i))
      (Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) =
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2)) <->
    (forall i, Membership.mem S i -> 0 < a i -> Or (y i = 0) (y i = 1)) := by
  classical
  let M := Finset.sum S (fun i => a i * y i)
  let D := M - Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))
  let E := Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2)
  constructor
  case mp =>
    intro hEq
    change sharpParityStabilityCost M D = E at hEq
    have hDzero : D = 0 := by
      by_contra hn
      have hs := finiteWeightedParity_sharp_stability_strict S a y ha hy hMoment hMass hn
      change sharpParityStabilityCost M D < E at hs
      linarith only [hs, hEq]
    have hEzero : E = 0 := by
      calc
        _ = sharpParityStabilityCost M D := hEq.symm
        _ = 0 := by rw [hDzero]; simp [sharpParityStabilityCost]
    intro i hi hai
    have hEach : forall j, Membership.mem S j ->
        0 <= a j * y j * (y j - 1) ^ 2 :=
      fun j hj => mul_nonneg (mul_nonneg (ha j hj) (hy j hj)) (sq_nonneg _)
    have hTermLe := Finset.single_le_sum hEach hi
    change a i * y i * (y i - 1) ^ 2 <= E at hTermLe
    have hTermZero : a i * y i * (y i - 1) ^ 2 = 0 := by
      rw [hEzero] at hTermLe
      exact le_antisymm hTermLe (hEach i hi)
    rcases mul_eq_zero.mp hTermZero with hAY | hSquare
    case inl =>
      have hY : y i = 0 := (mul_eq_zero.mp hAY).resolve_left hai.ne'
      exact Or.inl hY
    case inr =>
      exact Or.inr (by nlinarith only [hSquare])
  case mpr =>
    intro hSupport
    have hMK : M = Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hA : a i = 0
      case pos => simp [hA]
      case neg =>
        have hAPos : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hA)
        rcases hSupport i hi hAPos with hY | hY
        case inl =>
          simp [hY, momentRoundIndicator, not_le_of_gt momentRoundThreshold_bounds.1]
        case inr =>
          have hd : momentRoundThreshold <= 1 := by
            have hh := momentRoundThreshold_bounds.2
            linarith
          simp [hY, momentRoundIndicator, hd]
    have hDzero : D = 0 := by dsimp only [D]; rw [hMK]; ring
    have hEzero : E = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hA : a i = 0
      case pos => simp [hA]
      case neg =>
        have hAPos : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hA)
        rcases hSupport i hi hAPos with hY | hY
        case inl => simp [hY]
        case inr => simp [hY]
    change sharpParityStabilityCost M D = E
    rw [hDzero, hEzero]
    simp [sharpParityStabilityCost]

theorem finiteWeightedParity_sharp_stability_scaled_strict {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> 0 <= x i)
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i))
    (hDiscrepancy : Not ((Finset.sum S (fun i => a i * x i) / t -
      Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t))) = 0)) :
    sharpParityStabilityCost (Finset.sum S (fun i => a i * x i) / t)
      (Finset.sum S (fun i => a i * x i) / t -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t))) *
      t ^ 3 < Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
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
  have hCost := finiteWeightedParity_sharp_stability_strict S a (fun i => x i / t)
    ha (fun i hi => div_nonneg (hx i hi) (le_of_lt ht)) hNormalized hNormalizedMass
    (by rw [finiteWeighted_div_sum]; exact hDiscrepancy)
  rw [finiteWeighted_div_sum] at hCost
  have hScaled := _root_.mul_lt_mul_of_pos_right hCost (pow_pos ht 3)
  have hEnergy : t ^ 3 * Finset.sum S (fun i => a i * (x i / t) * (x i / t - 1) ^ 2) =
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := congrArg (fun q : Real => a i * q) (finiteWeighted_rescale_energy (x i) t ht)
    nlinarith only [h]
  nlinarith only [hScaled, hEnergy]

theorem threeLineWeightedSharpParityStability_charge_strict {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i))
    (hDiscrepancy : Not ((Finset.sum S (fun i => a i * x i) / t -
      Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t))) = 0)) :
    threeLineCharge * Finset.sum S a +
      threeLineSizeBiasedProfile t * Finset.sum S (fun i => a i * x i) +
      threeLineParityCubicCoefficient * t ^ 3 *
        sharpParityStabilityCost (Finset.sum S (fun i => a i * x i) / t)
          (Finset.sum S (fun i => a i * x i) / t -
            Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t))) <
      Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) := by
  have hCost := finiteWeightedParity_sharp_stability_scaled_strict S a x t ht ha
    (fun i hi => (hx i hi).1) hMoment hMass hDiscrepancy
  have hTau := threeLineParityCubicCoefficient_pos
  have hScaled := _root_.mul_lt_mul_of_pos_left hCost hTau
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
