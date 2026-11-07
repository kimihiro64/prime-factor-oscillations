/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelShiftedParity
import PrimeFactorOscillations.Helpers.ThresholdNonlinearTransfer

/-! # The complete nonlinear threshold charge for actual zero clusters -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem zeta_finite_nonlinear_threshold_domain (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (0 < (zetaCompensatedThresholdOrder W : Real))
      (momentRoundThreshold * (zetaCompensatedThresholdOrder W : Real) <
        zetaFiniteHorizontalEffectiveMass W) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hd : momentRoundThreshold < 1 := by
    have hh := momentRoundThreshold_bounds.2
    linarith only [hh]
  have ha : forall w, Membership.mem W w -> 0 <= (analyticOrderNatAt riemannZeta w : Real) :=
    fun _ _ => Nat.cast_nonneg _
  have hx : forall w, Membership.mem W w -> 0 <= (w.re - 1 / 2) ^ 2 :=
    fun _ _ => sq_nonneg _
  have hCenter : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2) ^ 2) = zetaFiniteHorizontalMomentRatio W * zetaFiniteHorizontalMoment W := by
    rw [zetaFiniteHorizontalFourthMoment_nested]
    unfold zetaFiniteHorizontalMomentRatio
    field_simp [hM.ne']
  have hDomain := finiteWeightedThreshold_scaled_domain W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    momentRoundThreshold hd (zetaFiniteHorizontalMomentRatio W) hBounds.2.1 ha hx hCenter hM
  unfold thresholdSelectedMass at hDomain
  rw [<- zetaCompensatedThresholdOrder_cast W hBounds.2.1] at hDomain
  change And (0 < (zetaCompensatedThresholdOrder W : Real))
    (momentRoundThreshold * (zetaCompensatedThresholdOrder W : Real) <
      zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W) at hDomain
  have hEffective : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  rw [hEffective] at hDomain
  exact hDomain

theorem zeta_finite_nonlinear_threshold_bound (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (Even (zetaCompensatedThresholdOrder W))
      (threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
          (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
        threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
          thresholdNonlinearCost momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
            (zetaCompensatedThresholdOrder W : Real) <=
          threeLineCharge * threeLineMultiplicityBudget height) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have htMax := zetaFiniteHorizontalMomentRatio_strip W hCritical hM
  have hd : And (0 < momentRoundThreshold) (momentRoundThreshold < 1) :=
    And.intro momentRoundThreshold_bounds.1 (by have hh := momentRoundThreshold_bounds.2; linarith)
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
  have hStrong := threeLineWeightedNonlinearThreshold_charge W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    momentRoundThreshold hd (zetaFiniteHorizontalMomentRatio W) hBounds.2.1 htMax ha hx hCenter hM
  unfold thresholdSelectedMass at hStrong
  rw [<- zetaCompensatedThresholdOrder_cast W hBounds.2.1] at hStrong
  change threeLineCharge * zetaFiniteMultiplicityMass W +
    threeLineSizeBiasedProfile (zetaFiniteHorizontalMomentRatio W) * zetaFiniteHorizontalMoment W +
    threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      thresholdNonlinearCost momentRoundThreshold
        (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W)
        (zetaCompensatedThresholdOrder W : Real) <= _ at hStrong
  have hEffective : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
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

theorem zeta_nonlinear_threshold_explicit_gain (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
        (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
      threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
        directionalParityStabilityCost (zetaFiniteHorizontalEffectiveMass W)
          (zetaFiniteHorizontalEffectiveMass W - (zetaCompensatedThresholdOrder W : Real)) +
      threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
        thresholdNonlinearGain (zetaFiniteHorizontalEffectiveMass W)
          (zetaCompensatedThresholdOrder W : Real) <=
      threeLineCharge * threeLineMultiplicityBudget height := by
  have hBound := (zeta_finite_nonlinear_threshold_bound height hHeight W
    hCritical hSame hReflect hN hM).2
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hKappa : 0 < zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalEffectiveMass
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hDomain := zeta_finite_nonlinear_threshold_domain W hCritical hN hM
  rw [thresholdNonlinearGain_identity _ _ hKappa hDomain.1 hDomain.2] at hBound
  simpa only [mul_add, add_assoc] using hBound

theorem zeta_nonlinear_threshold_gain_pos (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hDifferent : Not ((zetaFiniteHorizontalEffectiveMass W -
      (zetaCompensatedThresholdOrder W : Real)) = 0)) :
    0 < threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      thresholdNonlinearGain (zetaFiniteHorizontalEffectiveMass W)
        (zetaCompensatedThresholdOrder W : Real) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hKappa : 0 < zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalEffectiveMass
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hDomain := zeta_finite_nonlinear_threshold_domain W hCritical hN hM
  have hDifferentK : Not ((zetaCompensatedThresholdOrder W : Real) = zetaFiniteHorizontalEffectiveMass W) := by
    intro hEq
    apply hDifferent
    rw [hEq]
    ring
  have hGain := thresholdNonlinearGain_pos _ _ hKappa hDomain.1 hDomain.2 hDifferentK
  exact mul_pos (mul_pos threeLineParityCubicCoefficient_pos (pow_pos hBounds.2.1 3)) hGain

end PrimeFactorOscillations
