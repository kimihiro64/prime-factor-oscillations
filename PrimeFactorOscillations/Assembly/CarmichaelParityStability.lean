/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelClusterMultiplicity
import PrimeFactorOscillations.Assembly.CarmichaelKernelParityMultiplicity
import PrimeFactorOscillations.Helpers.CompensatedMomentParityStability

/-! # Finite-height stability of the compensated parity charge -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem zeta_effective_mass_le_height_budget (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    zetaFiniteHorizontalEffectiveMass W <= threeLineMultiplicityBudget height := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hFeasible := zetaFiniteHorizontalMoments_feasible W hN
  have hCancel : zetaFiniteHorizontalEffectiveMass W * zetaFiniteHorizontalFourthMoment W =
      (zetaFiniteHorizontalMoment W) ^ 2 := by
    unfold zetaFiniteHorizontalEffectiveMass
    field_simp [hBounds.1.ne']
  have hEffective : zetaFiniteHorizontalEffectiveMass W <= zetaFiniteMultiplicityMass W := by
    by_contra hNot
    have hBad := lt_of_not_ge hNot
    have hProduct := _root_.mul_lt_mul_of_pos_right hBad hBounds.1
    nlinarith only [hProduct, hCancel, hFeasible]
  have hWindow : forall w, Membership.mem W w -> abs (height - w.im) <= (0 : Real) := by
    intro w hw
    rw [hSame w hw]
    norm_num
  have hCount := zeta_finite_cluster_window_count height hHeight W hCritical 0
    (by simpa using threeLineCharge_pos) hWindow
  have hBudget : zetaFiniteMultiplicityMass W <= threeLineMultiplicityBudget height := by
    simpa [threeLineCharge_pos.ne'] using hCount
  exact le_trans hEffective hBudget

theorem zeta_finite_parity_stability_bound (height : Real) (hHeight : 2 <= abs height)
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
          compensatedParityStabilityCost (zetaFiniteHorizontalEffectiveMass W)
            (zetaFiniteHorizontalEffectiveMass W - (zetaCompensatedThresholdOrder W : Real)) <=
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
  have hStrong := threeLineWeightedParityStability_charge W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    (zetaFiniteHorizontalMomentRatio W) hBounds.2.1 htMax ha hx hCenter hM
  rw [<- zetaCompensatedThresholdOrder_cast W hBounds.2.1] at hStrong
  change threeLineCharge * zetaFiniteMultiplicityMass W +
    threeLineSizeBiasedProfile (zetaFiniteHorizontalMomentRatio W) * zetaFiniteHorizontalMoment W +
    threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      compensatedParityStabilityCost
        (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W)
        (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W -
          (zetaCompensatedThresholdOrder W : Real)) <= _ at hStrong
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

theorem zeta_parity_stability_odd_effective_gap (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (j : Nat) (hOdd : Odd j) (hEffective : zetaFiniteHorizontalEffectiveMass W = (j : Real)) :
    threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
        (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
      threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
        (momentRoundThreshold + (momentRoundThreshold - 1 / 4) /
          zetaFiniteHorizontalEffectiveMass W) <=
        threeLineCharge * threeLineMultiplicityBudget height := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hMass : 0 < zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalEffectiveMass
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hGap := odd_even_real_abs_gap j (zetaCompensatedThresholdOrder W) hOdd
    (zetaCompensatedThresholdOrder_parity W hCritical hReflect).2
  rw [<- hEffective] at hGap
  have hUnit := compensatedParityStabilityCost_unit_budget
    (zetaFiniteHorizontalEffectiveMass W) (zetaFiniteHorizontalEffectiveMass W)
    (zetaFiniteHorizontalEffectiveMass W - (zetaCompensatedThresholdOrder W : Real))
    hMass (le_refl _) hGap
  have hCoefficient : 0 <= threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 :=
    mul_nonneg (le_of_lt threeLineParityCubicCoefficient_pos)
      (pow_nonneg (le_of_lt hBounds.2.1) 3)
  have hScaled := _root_.mul_le_mul_of_nonneg_left hUnit hCoefficient
  have hMain := (zeta_finite_parity_stability_bound height hHeight W
    hCritical hSame hReflect hN hM).2
  nlinarith only [hScaled, hMain]

theorem zeta_parity_stability_odd_height_gap (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (j : Nat) (hOdd : Odd j) (hEffective : zetaFiniteHorizontalEffectiveMass W = (j : Real)) :
    threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
        (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
      threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
        (momentRoundThreshold + (momentRoundThreshold - 1 / 4) /
          threeLineMultiplicityBudget height) <=
        threeLineCharge * threeLineMultiplicityBudget height := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hMass : 0 < zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalEffectiveMass
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hBudget := zeta_effective_mass_le_height_budget height hHeight W hCritical hSame hN hM
  have hGap := odd_even_real_abs_gap j (zetaCompensatedThresholdOrder W) hOdd
    (zetaCompensatedThresholdOrder_parity W hCritical hReflect).2
  rw [<- hEffective] at hGap
  have hUnit := compensatedParityStabilityCost_unit_budget
    (zetaFiniteHorizontalEffectiveMass W) (threeLineMultiplicityBudget height)
    (zetaFiniteHorizontalEffectiveMass W - (zetaCompensatedThresholdOrder W : Real))
    hMass hBudget hGap
  have hCoefficient : 0 <= threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 :=
    mul_nonneg (le_of_lt threeLineParityCubicCoefficient_pos)
      (pow_nonneg (le_of_lt hBounds.2.1) 3)
  have hScaled := _root_.mul_le_mul_of_nonneg_left hUnit hCoefficient
  have hMain := (zeta_finite_parity_stability_bound height hHeight W
    hCritical hSame hReflect hN hM).2
  nlinarith only [hScaled, hMain]

theorem zeta_parity_stability_odd_combined_gap (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (j : Nat) (hOdd : Odd j) (hEffective : zetaFiniteHorizontalEffectiveMass W = (j : Real)) :
    threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
        (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
      (zetaFiniteHorizontalMomentRatio W) ^ 3 *
        max (threeLineKernelParityCoefficient (zetaFiniteHorizontalMomentRatio W))
          (threeLineParityCubicCoefficient *
            (momentRoundThreshold + (momentRoundThreshold - 1 / 4) /
              threeLineMultiplicityBudget height)) <=
        threeLineCharge * threeLineMultiplicityBudget height := by
  have hOld := zeta_kernel_parity_odd_effective_gap height hHeight W
    hCritical hSame hReflect hN hM j hOdd hEffective
  have hNew := zeta_parity_stability_odd_height_gap height hHeight W
    hCritical hSame hReflect hN hM j hOdd hEffective
  by_cases hCompare :
      threeLineKernelParityCoefficient (zetaFiniteHorizontalMomentRatio W) <=
        threeLineParityCubicCoefficient *
          (momentRoundThreshold + (momentRoundThreshold - 1 / 4) /
            threeLineMultiplicityBudget height)
  case pos =>
    rw [max_eq_right hCompare]
    nlinarith only [hNew]
  case neg =>
    rw [max_eq_left (le_of_not_ge hCompare)]
    nlinarith only [hOld]

end PrimeFactorOscillations
