/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelThresholdSharpness
import PrimeFactorOscillations.Helpers.NegativeThresholdTransfer

/-! # Both arithmetic costs in the complete signed actual zero-cluster bound -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem zeta_positive_threshold_even_mass (W : Finset Complex) (h t : Real) (hh : 0 < h)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w)) :
    exists m : Nat, thresholdSelectedMass h W (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / t) = 2 * (m : Real) := by
  classical
  let S := W.filter (fun w => h <= (w.re - 1 / 2) ^ 2 / t)
  have hCriticalS (w : Complex) (hw : Membership.mem S w) : And (0 < w.re) (w.re < 1) :=
    hCritical w (Finset.mem_filter.mp hw).1
  have hReflectS : forall w, Membership.mem S w -> Membership.mem S (zetaHorizontalReflection w) := by
    intro w hw
    have hm := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    apply And.intro (hReflect w hm.1)
    rw [zetaHorizontalCoord_reflection, neg_sq]
    exact hm.2
  have hNotOdd : Not (Odd (zetaFiniteTotalOrder S)) := by
    intro ho
    choose w hw hre _hOrder using zeta_odd_total_order_has_critical_point S hCriticalS hReflectS ho
    have hMem := (Finset.mem_filter.mp hw).2
    simp only [hre, sub_self, zero_pow (by decide : Not (2 = 0)), zero_div] at hMem
    linarith only [hMem, hh]
  have hMod : zetaFiniteTotalOrder S % 2 = 0 := by
    by_contra h
    have hOne : zetaFiniteTotalOrder S % 2 = 1 := by omega
    exact hNotOdd (Nat.odd_iff.mpr hOne)
  have hEven : Even (zetaFiniteTotalOrder S) := by
    apply Exists.intro (zetaFiniteTotalOrder S / 2)
    omega
  have hCast : (zetaFiniteTotalOrder S : Real) = thresholdSelectedMass h W
      (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2 / t) := by
    rw [zetaFiniteTotalOrder_cast]
    dsimp [S]
    unfold thresholdSelectedMass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w _
    simp only [momentRoundIndicator, mul_ite, mul_one, mul_zero]
  choose m hm using hEven
  rw [hm] at hCast
  push_cast at hCast
  exact Exists.intro m (by linarith only [hCast])

theorem zeta_finite_negative_integer_bound (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hMK : zetaFiniteHorizontalEffectiveMass W < (zetaCompensatedThresholdOrder W : Real)) :
    And (Even (zetaCompensatedThresholdOrder W))
      (threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
          (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
        threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
          (thresholdNonlinearCost momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
            (zetaCompensatedThresholdOrder W : Real) +
            thresholdNegativeIntegerCorrection momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
              (zetaCompensatedThresholdOrder W : Real)) <=
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
  have hEffective : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  have hKNormal : thresholdSelectedMass momentRoundThreshold W
      (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) =
        (zetaCompensatedThresholdOrder W : Real) := by
    unfold thresholdSelectedMass
    exact (zetaCompensatedThresholdOrder_cast W hBounds.2.1).symm
  have hSide : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W <
      thresholdSelectedMass momentRoundThreshold W (fun w => (analyticOrderNatAt riemannZeta w : Real))
        (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) := by
    rw [hEffective, hKNormal]
    exact hMK
  have hDomain := zeta_finite_nonlinear_threshold_domain W hCritical hN hM
  have hz := thresholdNegativeRoot_ge_one momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
    (zetaCompensatedThresholdOrder W : Real) hd.1 hDomain.2 hMK.le
  have hHighPositive : 0 < negativeThresholdHigh momentRoundThreshold
      (thresholdNegativeRoot momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
        (zetaCompensatedThresholdOrder W : Real)) := by
    unfold negativeThresholdHigh
    linarith only [hd.1, hz]
  have hHighEven : exists m : Nat, thresholdSelectedMass (negativeThresholdHigh momentRoundThreshold
      (thresholdNegativeRoot momentRoundThreshold (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W)
        (thresholdSelectedMass momentRoundThreshold W (fun w => (analyticOrderNatAt riemannZeta w : Real))
          (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W)))) W
      (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) = 2 * (m : Real) := by
    rw [hEffective, hKNormal]
    exact zeta_positive_threshold_even_mass W _ _ hHighPositive hCritical hReflect
  have hStrong := threeLineWeightedNegativeInteger_charge W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    momentRoundThreshold hd (zetaFiniteHorizontalMomentRatio W) hBounds.2.1 htMax ha hx hCenter hM hSide hHighEven
  unfold thresholdSelectedMass at hStrong
  rw [<- zetaCompensatedThresholdOrder_cast W hBounds.2.1] at hStrong
  change threeLineCharge * zetaFiniteMultiplicityMass W +
    threeLineSizeBiasedProfile (zetaFiniteHorizontalMomentRatio W) * zetaFiniteHorizontalMoment W +
    threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      (thresholdNonlinearCost momentRoundThreshold
        (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W)
        (zetaCompensatedThresholdOrder W : Real) +
        thresholdNegativeIntegerCorrection momentRoundThreshold
          (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W)
          (zetaCompensatedThresholdOrder W : Real)) <= _ at hStrong
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

theorem zeta_finite_two_sided_integer_bound (height : Real) (hHeight : 2 <= abs height)
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
          (thresholdNonlinearCost momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
            (zetaCompensatedThresholdOrder W : Real) +
            thresholdTwoSidedIntegerCorrection momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
              (zetaCompensatedThresholdOrder W : Real)) <=
          threeLineCharge * threeLineMultiplicityBudget height) := by
  by_cases h : (zetaCompensatedThresholdOrder W : Real) <= zetaFiniteHorizontalEffectiveMass W
  case pos =>
    have hb := zeta_finite_integer_threshold_bound height hHeight W hCritical hSame hReflect hN hM
    have hZero : thresholdNegativeIntegerCorrection momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
        (zetaCompensatedThresholdOrder W : Real) = 0 := by
      unfold thresholdNegativeIntegerCorrection
      rw [if_neg (not_lt.mpr h)]
    simpa only [thresholdTwoSidedIntegerCorrection, hZero, add_zero] using hb
  case neg =>
    have hb := zeta_finite_negative_integer_bound height hHeight W hCritical hSame hReflect hN hM (lt_of_not_ge h)
    have hZero : thresholdIntegerCorrection momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
        (zetaCompensatedThresholdOrder W : Real) = 0 := by
      unfold thresholdIntegerCorrection
      rw [if_neg h]
    simpa only [thresholdTwoSidedIntegerCorrection, hZero, zero_add] using hb

theorem zeta_two_sided_integer_explicit_gain (height : Real) (hHeight : 2 <= abs height)
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
          (zetaCompensatedThresholdOrder W : Real) +
      threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
        thresholdTwoSidedIntegerCorrection momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
          (zetaCompensatedThresholdOrder W : Real) <=
      threeLineCharge * threeLineMultiplicityBudget height := by
  have hBound := (zeta_finite_two_sided_integer_bound height hHeight W
    hCritical hSame hReflect hN hM).2
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hKappa : 0 < zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalEffectiveMass
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hDomain := zeta_finite_nonlinear_threshold_domain W hCritical hN hM
  rw [thresholdNonlinearGain_identity _ _ hKappa hDomain.1 hDomain.2] at hBound
  simpa only [mul_add, add_assoc] using hBound

theorem zeta_negative_integer_gain_pos (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hMK : zetaFiniteHorizontalEffectiveMass W < (zetaCompensatedThresholdOrder W : Real))
    (hGap : 0 < thresholdBandGap
      (thresholdNegativeRoot momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
        (zetaCompensatedThresholdOrder W : Real) - momentRoundThreshold)
      (zetaFiniteHorizontalEffectiveMass W - momentRoundThreshold * (zetaCompensatedThresholdOrder W : Real))) :
    0 < threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      thresholdNegativeIntegerCorrection momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
        (zetaCompensatedThresholdOrder W : Real) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hd : And (0 < momentRoundThreshold) (momentRoundThreshold < 1) :=
    And.intro momentRoundThreshold_bounds.1 (by have hh := momentRoundThreshold_bounds.2; linarith)
  have hDomain := zeta_finite_nonlinear_threshold_domain W hCritical hN hM
  have hJ := thresholdNegativeIntegerCorrection_pos momentRoundThreshold _ _ hd hDomain.1 hDomain.2 hMK hGap
  exact mul_pos (mul_pos threeLineParityCubicCoefficient_pos (pow_pos hBounds.2.1 3)) hJ

theorem zeta_negative_integer_gain_pos_off_spectrum (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (k : Nat) (hk : 0 < k) (hK : zetaCompensatedThresholdOrder W = 2 * k)
    (hMK : zetaFiniteHorizontalEffectiveMass W < 2 * (k : Real))
    (hAvoid : forall l : Nat, 0 < l -> l < k ->
      Not (zetaFiniteHorizontalEffectiveMass W = negativeThresholdExceptionalMass momentRoundThreshold k l)) :
    0 < threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      thresholdNegativeIntegerCorrection momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
        (zetaCompensatedThresholdOrder W : Real) := by
  have hKCast : (zetaCompensatedThresholdOrder W : Real) = 2 * (k : Real) := by rw [hK]; push_cast; rfl
  have hd : And (0 < momentRoundThreshold) (momentRoundThreshold < 1) :=
    And.intro momentRoundThreshold_bounds.1 (by have hh := momentRoundThreshold_bounds.2; linarith)
  have hDomain := (zeta_finite_nonlinear_threshold_domain W hCritical hN hM).2
  rw [hKCast] at hDomain
  have hz := thresholdNegativeRoot_ge_one momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
    (2 * (k : Real)) hd.1 hDomain hMK.le
  have hg : 0 < thresholdNegativeRoot momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
      (2 * (k : Real)) - momentRoundThreshold := by linarith only [hz, hd.2]
  have hAway : forall l : Nat, Not (zetaFiniteHorizontalEffectiveMass W - momentRoundThreshold * (2 * (k : Real)) =
      2 * (thresholdNegativeRoot momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
        (2 * (k : Real)) - momentRoundThreshold) * (l : Real)) := by
    intro l hl
    have hc := thresholdEvenNegative_lattice_counts momentRoundThreshold _ k l hd hk hDomain hMK hl
    have hm := (thresholdEvenNegative_lattice_mass_iff momentRoundThreshold _ k l hd hk hDomain hMK hc).mp hl
    exact hAvoid l hc.1 hc.2 hm
  have hGap := thresholdBandGap_pos _ _ hg (sub_nonneg.mpr hDomain.le) hAway
  apply zeta_negative_integer_gain_pos W hCritical hN hM
    (by rw [hKCast]; exact hMK)
  simpa only [hKCast] using hGap

end PrimeFactorOscillations
