/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNegativeInteger
import PrimeFactorOscillations.Helpers.ThresholdFeasibilityExistence
import PrimeFactorOscillations.Helpers.ThresholdFeasibilityStability

/-! # Sharp selected-order feasibility for actual reflected zeta clusters -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem zeta_thresholdExcess_paired_square (W : Finset Complex) (d t : Real) (hd : 0 < d)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w)) :
    2 * Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      (thresholdExcess d ((w.re - 1 / 2) ^ 2 / t)) ^ 2) <=
      (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        thresholdExcess d ((w.re - 1 / 2) ^ 2 / t))) ^ 2 := by
  have hUnit : forall w, Membership.mem W w -> 0 < (analyticOrderNatAt riemannZeta w : Real) ->
      1 <= (analyticOrderNatAt riemannZeta w : Real) := by
    intro w _ hp
    have hn : 0 < analyticOrderNatAt riemannZeta w := by exact_mod_cast hp
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  apply finiteWeighted_paired_square W
    (fun w => (analyticOrderNatAt riemannZeta w : Real))
    (fun w => thresholdExcess d ((w.re - 1 / 2) ^ 2 / t))
    (fun _ _ => Nat.cast_nonneg _) (fun w _ => thresholdExcess_nonneg d _) hUnit
  intro w hw hp hxp
  have hNe : Not (w = zetaHorizontalReflection w) := by
    intro heq
    have hre := congrArg Complex.re heq
    rw [zetaHorizontalReflection_re] at hre
    have hc : w.re = 1 / 2 := by linarith only [hre]
    have hZero : thresholdExcess d ((w.re - 1 / 2) ^ 2 / t) = 0 := by
      simp [hc, thresholdExcess, momentRoundIndicator, not_le.mpr hd]
    rw [hZero] at hxp
    exact (lt_irrefl 0) hxp
  apply Exists.intro (zetaHorizontalReflection w)
  apply And.intro (hReflect w hw)
  apply And.intro hNe
  constructor
  case left =>
    rw [zetaOrder_reflection w (hCritical w hw)]
    exact hUnit w hw hp
  case right => rw [zetaHorizontalCoord_reflection, neg_sq]

theorem zeta_finite_threshold_quadratic (W : Finset Complex) (d : Real)
    (hd : And (0 < d) (d < 1))
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    (zetaFiniteHorizontalEffectiveMass W - d * thresholdSelectedMass d W
      (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W)) ^ 2 +
      (4 * d - 2) * zetaFiniteHorizontalEffectiveMass W - 2 * d ^ 2 * thresholdSelectedMass d W
      (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) >= 0 := by
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
  have h := finiteWeighted_threshold_quadratic W (fun w => (analyticOrderNatAt riemannZeta w : Real))
    (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) d hd.1.le
    (fun _ _ => Nat.cast_nonneg _)
    (fun w _ => div_nonneg (sq_nonneg (w.re - 1 / 2)) ht.le) hNormalized
    (zeta_thresholdExcess_paired_square W d (zetaFiniteHorizontalMomentRatio W) hd.1 hCritical hReflect)
  rw [finiteWeighted_div_sum] at h
  change (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W - d * _) ^ 2 +
    (4 * d - 2) * (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W) - 2 * d ^ 2 * _ >= 0 at h
  rw [hEffective] at h
  exact h

theorem zeta_finite_threshold_feasibility (W : Finset Complex) (d : Real)
    (hd : And (0 < d) (d < 1))
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (thresholdMinimumMass d (thresholdSelectedMass d W
      (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W)) <=
        zetaFiniteHorizontalEffectiveMass W)
      (thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
        (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) <=
          thresholdMaxSelected d (zetaFiniteHorizontalEffectiveMass W)) := by
  let K := thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
    (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W)
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hCenter : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2) ^ 2) = zetaFiniteHorizontalMomentRatio W * zetaFiniteHorizontalMoment W := by
    rw [zetaFiniteHorizontalFourthMoment_nested]
    unfold zetaFiniteHorizontalMomentRatio
    field_simp [hM.ne']
  have hEffective : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  have hDomain := finiteWeightedThreshold_scaled_domain W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    d hd.2 (zetaFiniteHorizontalMomentRatio W) hBounds.2.1
    (fun _ _ => Nat.cast_nonneg _) (fun w _ => sq_nonneg (w.re - 1 / 2)) hCenter hM
  change And (0 < K) (d * K < zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W) at hDomain
  rw [hEffective] at hDomain
  choose k hk using zeta_positive_threshold_even_mass W d (zetaFiniteHorizontalMomentRatio W)
    hd.1 hCritical hReflect
  change K = 2 * (k : Real) at hk
  have hkPos : 0 < k := by
    by_contra hn
    have hz : k = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz] at hk
    norm_num at hk
    linarith only [hk, hDomain.1]
  have hkOne : (1 : Real) <= (k : Real) := by exact_mod_cast hkPos
  have hK : 2 <= K := by rw [hk]; linarith only [hkOne]
  have hMass : 0 < zetaFiniteHorizontalEffectiveMass W := by
    rw [<- hEffective]
    exact div_pos hM hBounds.2.1
  have hP := zeta_finite_threshold_quadratic W d hd hCritical hReflect hN hM
  exact And.intro
    (thresholdQuadratic_mass_floor d (zetaFiniteHorizontalEffectiveMass W) K hd hK hDomain.2 hP)
    (thresholdQuadratic_inverse_count d (zetaFiniteHorizontalEffectiveMass W) K hd hMass hDomain.2 hP)

theorem zeta_compensated_order_inverse_bound (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (thresholdMinimumMass momentRoundThreshold (zetaCompensatedThresholdOrder W : Real) <=
      zetaFiniteHorizontalEffectiveMass W)
      ((zetaCompensatedThresholdOrder W : Real) <=
        thresholdMaxSelected momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)) := by
  have hd : And (0 < momentRoundThreshold) (momentRoundThreshold < 1) :=
    And.intro momentRoundThreshold_bounds.1 (by have hh := momentRoundThreshold_bounds.2; linarith)
  have ht := (zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM).2.1
  have hK : thresholdSelectedMass momentRoundThreshold W
      (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) =
        (zetaCompensatedThresholdOrder W : Real) := by
    unfold thresholdSelectedMass
    exact (zetaCompensatedThresholdOrder_cast W ht).symm
  have h := zeta_finite_threshold_feasibility W momentRoundThreshold hd hCritical hReflect hN hM
  rw [hK] at h
  exact h

end PrimeFactorOscillations
