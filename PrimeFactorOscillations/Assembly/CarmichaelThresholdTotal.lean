/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelThresholdFeasibility
import PrimeFactorOscillations.Helpers.ThresholdRadialPackingSharpness
import PrimeFactorOscillations.Helpers.ThresholdSelectedQuantum
import PrimeFactorOscillations.Helpers.ThresholdSeparatedSharpness
import PrimeFactorOscillations.Helpers.ThresholdSingleLevelCost
import PrimeFactorOscillations.Helpers.ThresholdSingleLevelSharpness
import PrimeFactorOscillations.Helpers.ThresholdTotalFeasibility
import PrimeFactorOscillations.Helpers.ThresholdTotalRateSharpness
import PrimeFactorOscillations.Helpers.ThresholdTotalStability
import PrimeFactorOscillations.Helpers.ThresholdTotalStabilitySharpness
import PrimeFactorOscillations.Helpers.ZetaThresholdCollision
import PrimeFactorOscillations.Helpers.ZetaThresholdRadialPacking

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

theorem zeta_finite_threshold_total_stability (W : Finset Complex) (d : Real)
    (hd : And (0 < d) (d < 1))
    (hStrip : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    let t := zetaFiniteHorizontalMomentRatio W
    let M := zetaFiniteHorizontalEffectiveMass W
    let N := zetaFiniteMultiplicityMass W
    let K := thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / t)
    let v := thresholdModelHigh (N - K) K d
    let D := (2 * v - 1) * (thresholdTotalUpper d N K - M)
    And (2 * (v - d) * Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      thresholdTotalLowDistance d ((w.re - 1 / 2) ^ 2 / t)) <= D)
      (And (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        thresholdTotalHighSquare d v ((w.re - 1 / 2) ^ 2 / t)) <= D)
        (forall phi : Real -> Real,
          (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
          abs (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
            phi ((w.re - 1 / 2) ^ 2 / t)) - thresholdTotalStatistic d v N K phi) <=
              D / (2 * (v - d)) + Real.sqrt (K * D))) := by
  dsimp only
  have hn := zeta_finite_normalized_horizontal_moments W hStrip hN hM
  have hMoment := hn.2.2.2.trans hn.2.2.1.symm
  have ha : forall w, Membership.mem W w -> 0 <= (analyticOrderNatAt riemannZeta w : Real) :=
    fun _ _ => Nat.cast_nonneg _
  have hDomain := finiteWeightedThreshold_domain W
    (fun w => (analyticOrderNatAt riemannZeta w : Real))
    (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) d hd.2 ha
    (fun w _ => div_nonneg (sq_nonneg _) hn.1.le) hMoment
    (by rw [hn.2.2.1]; exact hn.2.1)
  have hNew := finiteWeighted_threshold_total_stability W
    (fun w => (analyticOrderNatAt riemannZeta w : Real))
    (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) d hd ha hMoment hDomain.1
  rw [hn.2.2.1] at hNew
  exact hNew

theorem zeta_finite_selected_two_linear (W : Finset Complex) (d : Real)
    (hd : And (0 < d) (d < 1))
    (hStrip : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hSelected : thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) = 2) :
    let t := zetaFiniteHorizontalMomentRatio W
    let N := zetaFiniteMultiplicityMass W
    let v := thresholdModelHigh (N - 2) 2 d
    let Delta := thresholdTotalUpper d N 2 - zetaFiniteHorizontalEffectiveMass W
    let L := Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      thresholdTotalLowDistance d ((w.re - 1 / 2) ^ 2 / t))
    And (exists w : Complex, And (Membership.mem W w) (And (1 / 2 < w.re)
      (And (Membership.mem W (zetaHorizontalReflection w))
        (And (Not (w = zetaHorizontalReflection w))
          (And (analyticOrderNatAt riemannZeta w = 1)
            (analyticOrderNatAt riemannZeta (zetaHorizontalReflection w) = 1))))))
      (And (0 <= Delta)
        (And (abs (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
          abs ((w.re - 1 / 2) ^ 2 / t - v)) -
            thresholdTotalStatistic d v N 2 (fun z => abs (z - v))) = L + abs (Delta - L))
          (And (forall phi : Real -> Real,
            (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
            abs (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
              phi ((w.re - 1 / 2) ^ 2 / t)) - thresholdTotalStatistic d v N 2 phi) <=
                L + abs (Delta - L))
            (forall phi : Real -> Real,
              (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
              abs (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
                phi ((w.re - 1 / 2) ^ 2 / t)) - thresholdTotalStatistic d v N 2 phi) <=
                  thresholdSingleCoefficient d v * Delta)))) := by
  dsimp only
  have hn := zeta_finite_normalized_horizontal_moments W hStrip hN hM
  choose h hCut hDirac hPair using zeta_selected_two_dirac W d
    (zetaFiniteHorizontalMomentRatio W) hd.1 hn.1 hStrip hReflect hSelected
  choose w hw hRight hY hR hNe hOne hROne using hPair
  have hMoment := hn.2.2.2.trans hn.2.2.1.symm
  have ha : forall w, Membership.mem W w -> 0 <= (analyticOrderNatAt riemannZeta w : Real) :=
    fun _ _ => Nat.cast_nonneg _
  have hK : 0 < thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) := by
    rw [hSelected]
    norm_num
  have hNew := finiteWeighted_single_level_linear W
    (fun w => (analyticOrderNatAt riemannZeta w : Real))
    (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) d h hd ha hMoment hK hDirac
  rw [hn.2.2.1, hSelected] at hNew
  exact And.intro (Exists.intro w (And.intro hw (And.intro hRight
    (And.intro hR (And.intro hNe (And.intro hOne hROne)))))) hNew

theorem zeta_finite_selected_two_half (W : Finset Complex) (d : Real)
    (hd : And (0 < d) (d <= 1 / 2))
    (hStrip : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hSelected : thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) = 2) :
    let t := zetaFiniteHorizontalMomentRatio W
    let N := zetaFiniteMultiplicityMass W
    let v := thresholdModelHigh (N - 2) 2 d
    let Delta := thresholdTotalUpper d N 2 - zetaFiniteHorizontalEffectiveMass W
    And (abs (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      abs ((w.re - 1 / 2) ^ 2 / t - v)) -
        thresholdTotalStatistic d v N 2 (fun z => abs (z - v))) = Delta)
      (forall phi : Real -> Real,
        (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
        abs (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
          phi ((w.re - 1 / 2) ^ 2 / t)) - thresholdTotalStatistic d v N 2 phi) <= Delta) := by
  dsimp only
  have hn := zeta_finite_normalized_horizontal_moments W hStrip hN hM
  choose h hCut hDirac hPair using zeta_selected_two_dirac W d
    (zetaFiniteHorizontalMomentRatio W) hd.1 hn.1 hStrip hReflect hSelected
  have hMoment := hn.2.2.2.trans hn.2.2.1.symm
  have ha : forall w, Membership.mem W w -> 0 <= (analyticOrderNatAt riemannZeta w : Real) :=
    fun _ _ => Nat.cast_nonneg _
  have hK : 0 < thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) := by
    rw [hSelected]
    norm_num
  have hNew := finiteWeighted_single_level_half W
    (fun w => (analyticOrderNatAt riemannZeta w : Real))
    (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) d h hd ha hMoment hK hDirac
  rw [hn.2.2.1, hSelected] at hNew
  exact hNew

end PrimeFactorOscillations
