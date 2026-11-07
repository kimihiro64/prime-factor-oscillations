/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSharpParityStability
import PrimeFactorOscillations.Helpers.CompensatedParityRigidity

/-! # Strict compensated parity stability and closed-endpoint recovery -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem zeta_finite_sharp_parity_stability_strict (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hDiscrepancy : Not ((zetaFiniteHorizontalEffectiveMass W -
      (zetaCompensatedThresholdOrder W : Real)) = 0)) :
    And (Even (zetaCompensatedThresholdOrder W))
      (threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
          (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
        threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
          sharpParityStabilityCost (zetaFiniteHorizontalEffectiveMass W)
            (zetaFiniteHorizontalEffectiveMass W - (zetaCompensatedThresholdOrder W : Real)) <
          threeLineCharge * threeLineMultiplicityBudget height) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have htMax := zetaFiniteHorizontalMomentRatio_strip W hCritical hM
  have ha : forall w, Membership.mem W w -> 0 <= (analyticOrderNatAt riemannZeta w : Real) :=
    fun _ _ => Nat.cast_nonneg _
  have hx : forall w, Membership.mem W w ->
      And (0 <= (w.re - 1 / 2) ^ 2) ((w.re - 1 / 2) ^ 2 <= 1 / 4) :=
    fun w hw => zeta_horizontal_square_bounds w (hCritical w hw)
  have hCenter : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2) ^ 2) = zetaFiniteHorizontalMomentRatio W * zetaFiniteHorizontalMoment W := by
    rw [zetaFiniteHorizontalFourthMoment_nested]
    unfold zetaFiniteHorizontalMomentRatio
    field_simp [hM.ne']
  have hEffective : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  have hDScaled : Not ((Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      (w.re - 1 / 2) ^ 2) / zetaFiniteHorizontalMomentRatio W -
      Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        momentRoundIndicator momentRoundThreshold
          ((w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W))) = 0) := by
    rw [<- zetaCompensatedThresholdOrder_cast W hBounds.2.1]
    change Not ((zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W -
      (zetaCompensatedThresholdOrder W : Real)) = 0)
    rw [hEffective]
    exact hDiscrepancy
  have hStrong := threeLineWeightedSharpParityStability_charge_strict W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    (zetaFiniteHorizontalMomentRatio W) hBounds.2.1 htMax ha hx hCenter hM hDScaled
  rw [<- zetaCompensatedThresholdOrder_cast W hBounds.2.1] at hStrong
  change threeLineCharge * zetaFiniteMultiplicityMass W +
    threeLineSizeBiasedProfile (zetaFiniteHorizontalMomentRatio W) * zetaFiniteHorizontalMoment W +
    threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      sharpParityStabilityCost
        (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W)
        (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W -
          (zetaCompensatedThresholdOrder W : Real)) < _ at hStrong
  rw [hEffective] at hStrong
  have hCharge : threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
      (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) =
      threeLineCharge * zetaFiniteMultiplicityMass W +
        threeLineSizeBiasedProfile (zetaFiniteHorizontalMomentRatio W) * zetaFiniteHorizontalMoment W := by
    unfold threeLineMomentRatioCharge zetaFiniteHorizontalMomentRatio
    ring
  have hUpper := zeta_finite_horizontal_profile_upper height hHeight W hCritical hSame
  exact And.intro (zetaCompensatedThresholdOrder_parity W hCritical hReflect).1
    (by nlinarith only [hStrong, hUpper, hCharge])


theorem zeta_sharp_parity_closed_unit_bound (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hSlack : threeLineCharge * threeLineMultiplicityBudget height -
      threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
        (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) <=
      threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
        (momentRoundThreshold + sharpParityCoefficient / zetaFiniteHorizontalEffectiveMass W)) :
    abs (zetaFiniteHorizontalEffectiveMass W - (zetaCompensatedThresholdOrder W : Real)) < 1 := by
  let kappa := zetaFiniteHorizontalEffectiveMass W
  let D := kappa - (zetaCompensatedThresholdOrder W : Real)
  let B2 := threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
    (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W)
  let factor := threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hKappa : 0 < kappa := by
    dsimp only [kappa]
    unfold zetaFiniteHorizontalEffectiveMass
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hFactor : 0 < factor := mul_pos threeLineParityCubicCoefficient_pos (pow_pos hBounds.2.1 3)
  change threeLineCharge * threeLineMultiplicityBudget height - B2 <=
    factor * (momentRoundThreshold + sharpParityCoefficient / kappa) at hSlack
  change abs D < 1
  by_contra hn
  have hAbs : 1 <= abs D := le_of_not_gt hn
  have hD : Not (D = 0) := by
    intro hz
    rw [hz] at hAbs
    norm_num at hAbs
  have hStrong := (zeta_finite_sharp_parity_stability_strict height hHeight W
    hCritical hSame hReflect hN hM hD).2
  change B2 + factor * sharpParityStabilityCost kappa D <
    threeLineCharge * threeLineMultiplicityBudget height at hStrong
  have hSquare : 1 <= D ^ 2 := by
    nlinarith only [hAbs, sq_abs D, sq_nonneg (abs D - 1)]
  have hLinear := mul_nonneg momentRoundThreshold_bounds.1.le (sub_nonneg.mpr hAbs)
  have hQuadratic := div_nonneg
    (mul_nonneg sharpParityCoefficient_pos.le (sub_nonneg.mpr hSquare)) hKappa.le
  have hFloor : momentRoundThreshold + sharpParityCoefficient / kappa <=
      sharpParityStabilityCost kappa D := by
    have he : sharpParityCoefficient * (D ^ 2 - 1) / kappa =
        sharpParityCoefficient * D ^ 2 / kappa - sharpParityCoefficient / kappa := by ring
    rw [he] at hQuadratic
    unfold sharpParityStabilityCost
    linarith only [hLinear, hQuadratic]
  have hScaled := _root_.mul_le_mul_of_nonneg_left hFloor hFactor.le
  linarith only [hStrong, hScaled, hSlack]

theorem zeta_sharp_parity_closed_unique_even_order (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hSlack : threeLineCharge * threeLineMultiplicityBudget height -
      threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
        (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) <=
      threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
        (momentRoundThreshold + sharpParityCoefficient / zetaFiniteHorizontalEffectiveMass W)) :
    ExistsUnique (fun k : Nat => And (Even k)
      (abs (zetaFiniteHorizontalEffectiveMass W - (k : Real)) < 1)) := by
  have hEven := (zetaCompensatedThresholdOrder_parity W hCritical hReflect).1
  have hNear := zeta_sharp_parity_closed_unit_bound height hHeight W
    hCritical hSame hReflect hN hM hSlack
  refine ExistsUnique.intro (zetaCompensatedThresholdOrder W) (And.intro hEven hNear) ?_
  intro k hk
  exact evenNatural_unique_abs_lt_one (zetaFiniteHorizontalEffectiveMass W)
    k (zetaCompensatedThresholdOrder W) hk.1 hEven hk.2 hNear

end PrimeFactorOscillations
