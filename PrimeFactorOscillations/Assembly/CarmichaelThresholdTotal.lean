/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelThresholdFeasibility
import PrimeFactorOscillations.Helpers.ThresholdTotalFeasibility

/-! # The complete necessary total/selected-order region for actual zeta clusters -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem zeta_finite_threshold_total_upper (W : Finset Complex) (d : Real)
    (hd : And (0 < d) (d < 1))
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hLow : thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) < zetaFiniteMultiplicityMass W) :
    zetaFiniteHorizontalEffectiveMass W < thresholdTotalUpper d (zetaFiniteMultiplicityMass W)
      (thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
        (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W)) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have ht := hBounds.2.1
  have hCenter : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2) ^ 2) = zetaFiniteHorizontalMomentRatio W * zetaFiniteHorizontalMoment W := by
    rw [zetaFiniteHorizontalFourthMoment_nested]
    unfold zetaFiniteHorizontalMomentRatio
    field_simp [hM.ne']
  have hEffective : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  have hNormalized : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) ^ 2) =
      Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        ((w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W)) := by
    calc
      _ = Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
          ((w.re - 1 / 2) ^ 2) ^ 2) / (zetaFiniteHorizontalMomentRatio W) ^ 2 := by
        simp only [div_pow]
        exact finiteWeighted_div_sum W (fun w => (analyticOrderNatAt riemannZeta w : Real))
          (fun w => ((w.re - 1 / 2) ^ 2) ^ 2) ((zetaFiniteHorizontalMomentRatio W) ^ 2)
      _ = zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W := by
        rw [hCenter]
        field_simp [ht.ne']
      _ = _ := (finiteWeighted_div_sum W (fun w => (analyticOrderNatAt riemannZeta w : Real))
        (fun w => (w.re - 1 / 2) ^ 2) (zetaFiniteHorizontalMomentRatio W)).symm
  have ha : forall w, Membership.mem W w -> 0 <= (analyticOrderNatAt riemannZeta w : Real) :=
    fun _ _ => Nat.cast_nonneg _
  have hDomain := finiteWeightedThreshold_scaled_domain W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    d hd.2 (zetaFiniteHorizontalMomentRatio W) ht ha (fun w _ => sq_nonneg (w.re - 1 / 2)) hCenter hM
  have hUpper := finiteWeighted_threshold_total_upper W (fun w => (analyticOrderNatAt riemannZeta w : Real))
    (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) d hd ha hNormalized hDomain.1 hLow
  rw [finiteWeighted_div_sum] at hUpper
  change zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W < _ at hUpper
  rw [hEffective] at hUpper
  exact hUpper

theorem zeta_finite_threshold_total_region (W : Finset Complex) (d : Real)
    (hd : And (0 < d) (d < 1))
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    let K := thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W)
    And (thresholdMinimumMass d K <= zetaFiniteHorizontalEffectiveMass W)
      (And (K <= thresholdMaxSelected d (zetaFiniteHorizontalEffectiveMass W))
        (And (K <= zetaFiniteMultiplicityMass W)
          (if K = zetaFiniteMultiplicityMass W then
            zetaFiniteHorizontalEffectiveMass W <= zetaFiniteMultiplicityMass W
           else zetaFiniteHorizontalEffectiveMass W < thresholdTotalUpper d (zetaFiniteMultiplicityMass W) K))) := by
  let K := thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
    (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W)
  have hOld := zeta_finite_threshold_feasibility W d hd hCritical hReflect hN hM
  have hKN : K <= zetaFiniteMultiplicityMass W := by
    unfold K thresholdSelectedMass zetaFiniteMultiplicityMass
    apply Finset.sum_le_sum
    intro w _
    by_cases hCut : d <= (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W
    case pos =>
      simpa only [momentRoundIndicator, if_pos hCut, mul_one] using
        (_root_.le_refl (analyticOrderNatAt riemannZeta w : Real))
    case neg =>
      simpa only [momentRoundIndicator, if_neg hCut, mul_zero] using
        (Nat.cast_nonneg (analyticOrderNatAt riemannZeta w) : (0 : Real) <= _)
  have hFace : if K = zetaFiniteMultiplicityMass W then
      zetaFiniteHorizontalEffectiveMass W <= zetaFiniteMultiplicityMass W
      else zetaFiniteHorizontalEffectiveMass W < thresholdTotalUpper d (zetaFiniteMultiplicityMass W) K := by
    by_cases heq : K = zetaFiniteMultiplicityMass W
    case pos =>
      simp only [if_pos heq]
      have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
      have hFeasible := zetaFiniteHorizontalMoments_feasible W hN
      have hCancel : zetaFiniteHorizontalEffectiveMass W * zetaFiniteHorizontalFourthMoment W =
          (zetaFiniteHorizontalMoment W) ^ 2 := by
        unfold zetaFiniteHorizontalEffectiveMass
        field_simp [hBounds.1.ne']
      by_contra hn
      have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hBounds.1
      nlinarith only [hp, hCancel, hFeasible]
    case neg =>
      simp only [if_neg heq]
      have hStrict : K < zetaFiniteMultiplicityMass W := by
        by_contra hn
        exact heq (le_antisymm hKN (le_of_not_gt hn))
      exact zeta_finite_threshold_total_upper W d hd hCritical hN hM hStrict
  exact And.intro hOld.1 (And.intro hOld.2 (And.intro hKN hFace))

theorem zeta_compensated_order_total_region (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (thresholdMinimumMass momentRoundThreshold (zetaCompensatedThresholdOrder W : Real) <=
      zetaFiniteHorizontalEffectiveMass W)
      (And ((zetaCompensatedThresholdOrder W : Real) <=
          thresholdMaxSelected momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W))
        (And ((zetaCompensatedThresholdOrder W : Real) <= zetaFiniteMultiplicityMass W)
          (if (zetaCompensatedThresholdOrder W : Real) = zetaFiniteMultiplicityMass W then
            zetaFiniteHorizontalEffectiveMass W <= zetaFiniteMultiplicityMass W
           else zetaFiniteHorizontalEffectiveMass W < thresholdTotalUpper momentRoundThreshold
            (zetaFiniteMultiplicityMass W) (zetaCompensatedThresholdOrder W : Real)))) := by
  have hd : And (0 < momentRoundThreshold) (momentRoundThreshold < 1) :=
    And.intro momentRoundThreshold_bounds.1 (by have hh := momentRoundThreshold_bounds.2; linarith)
  have ht := (zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM).2.1
  have hK : thresholdSelectedMass momentRoundThreshold W
      (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) =
        (zetaCompensatedThresholdOrder W : Real) := by
    unfold thresholdSelectedMass
    exact (zetaCompensatedThresholdOrder_cast W ht).symm
  have h := zeta_finite_threshold_total_region W momentRoundThreshold hd hCritical hReflect hN hM
  dsimp only at h
  rw [hK] at h
  exact h

end PrimeFactorOscillations
