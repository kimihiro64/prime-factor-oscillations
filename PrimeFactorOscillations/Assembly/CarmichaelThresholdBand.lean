/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNonlinearThreshold
import PrimeFactorOscillations.Helpers.ThresholdBandSharpness
import PrimeFactorOscillations.Helpers.ThresholdBandTransfer

/-! # Even interior bands and the complete signed arithmetic gain -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def zetaThresholdBandSet (W : Finset Complex) (d t : Real) : Finset Complex := by
  classical
  exact W.filter (fun w => And (d / 2 <= (w.re - 1 / 2) ^ 2 / t)
    ((w.re - 1 / 2) ^ 2 / t < d))

def zetaThresholdBandOrder (W : Finset Complex) (d t : Real) : Nat :=
  zetaFiniteTotalOrder (zetaThresholdBandSet W d t)

theorem zetaThresholdBandOrder_cast (W : Finset Complex) (d t : Real) :
    (zetaThresholdBandOrder W d t : Real) = thresholdBandMass d W
      (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2 / t) := by
  classical
  unfold zetaThresholdBandOrder
  rw [zetaFiniteTotalOrder_cast]
  unfold zetaThresholdBandSet thresholdBandMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  simp only [thresholdBandIndicator, mul_ite, mul_one, mul_zero]

theorem zetaThresholdBandOrder_even (W : Finset Complex) (d t : Real) (hd : 0 < d)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w)) :
    Even (zetaThresholdBandOrder W d t) := by
  classical
  have hCriticalS (w : Complex) (hw : Membership.mem (zetaThresholdBandSet W d t) w) :
      And (0 < w.re) (w.re < 1) := hCritical w (Finset.mem_filter.mp hw).1
  have hReflectS : forall w, Membership.mem (zetaThresholdBandSet W d t) w ->
      Membership.mem (zetaThresholdBandSet W d t) (zetaHorizontalReflection w) := by
    intro w hw
    have hm := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    apply And.intro (hReflect w hm.1)
    rw [zetaHorizontalCoord_reflection, neg_sq]
    exact hm.2
  have hNotOdd : Not (Odd (zetaThresholdBandOrder W d t)) := by
    intro ho
    choose w hw hre _hOrder using zeta_odd_total_order_has_critical_point
      (zetaThresholdBandSet W d t) hCriticalS hReflectS ho
    have hBand := (Finset.mem_filter.mp hw).2.1
    simp only [hre, sub_self, zero_pow (by decide : Not (2 = 0)), zero_div] at hBand
    linarith only [hBand, hd]
  have hMod : zetaThresholdBandOrder W d t % 2 = 0 := by
    by_contra h
    have hOne : zetaThresholdBandOrder W d t % 2 = 1 := by omega
    exact hNotOdd (Nat.odd_iff.mpr hOne)
  apply Exists.intro (zetaThresholdBandOrder W d t / 2)
  omega

theorem zetaThresholdBand_even_mass (W : Finset Complex) (d t : Real) (hd : 0 < d)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w)) :
    exists m : Nat, thresholdBandMass d W
      (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2 / t) = 2 * (m : Real) := by
  choose m hm using zetaThresholdBandOrder_even W d t hd hCritical hReflect
  have hc := zetaThresholdBandOrder_cast W d t
  rw [hm] at hc
  push_cast at hc
  exact Exists.intro m (by linarith only [hc])

theorem zeta_finite_integer_threshold_bound (height : Real) (hHeight : 2 <= abs height)
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
            thresholdIntegerCorrection momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
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
  have hStrong := threeLineWeightedIntegerThreshold_charge W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    momentRoundThreshold hd (zetaFiniteHorizontalMomentRatio W) hBounds.2.1 htMax ha hx hCenter hM
      (zetaThresholdBand_even_mass W momentRoundThreshold (zetaFiniteHorizontalMomentRatio W) hd.1 hCritical hReflect)
  unfold thresholdSelectedMass at hStrong
  rw [<- zetaCompensatedThresholdOrder_cast W hBounds.2.1] at hStrong
  change threeLineCharge * zetaFiniteMultiplicityMass W +
    threeLineSizeBiasedProfile (zetaFiniteHorizontalMomentRatio W) * zetaFiniteHorizontalMoment W +
    threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      (thresholdNonlinearCost momentRoundThreshold
        (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W)
        (zetaCompensatedThresholdOrder W : Real) +
        thresholdIntegerCorrection momentRoundThreshold
          (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W)
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

theorem zeta_integer_threshold_explicit_gain (height : Real) (hHeight : 2 <= abs height)
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
        thresholdIntegerCorrection momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
          (zetaCompensatedThresholdOrder W : Real) <=
      threeLineCharge * threeLineMultiplicityBudget height := by
  have hBound := (zeta_finite_integer_threshold_bound height hHeight W
    hCritical hSame hReflect hN hM).2
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hKappa : 0 < zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalEffectiveMass
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hDomain := zeta_finite_nonlinear_threshold_domain W hCritical hN hM
  rw [thresholdNonlinearGain_identity _ _ hKappa hDomain.1 hDomain.2] at hBound
  simpa only [mul_add, add_assoc] using hBound

theorem zeta_integer_threshold_gain_pos (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hKM : (zetaCompensatedThresholdOrder W : Real) <= zetaFiniteHorizontalEffectiveMass W)
    (hGap : 0 < thresholdBandGap momentRoundThreshold
      (zetaFiniteHorizontalEffectiveMass W - (zetaCompensatedThresholdOrder W : Real) *
        thresholdPositiveRoot momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
          (zetaCompensatedThresholdOrder W : Real))) :
    0 < threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      thresholdIntegerCorrection momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
        (zetaCompensatedThresholdOrder W : Real) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hKappa : 0 < zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalEffectiveMass
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hd : And (0 < momentRoundThreshold) (momentRoundThreshold < 1) :=
    And.intro momentRoundThreshold_bounds.1 (by have hh := momentRoundThreshold_bounds.2; linarith)
  have hDomain := zeta_finite_nonlinear_threshold_domain W hCritical hN hM
  have hGain := thresholdIntegerCorrection_pos momentRoundThreshold _ _ hd hKappa hDomain.1 hKM hGap
  exact mul_pos (mul_pos threeLineParityCubicCoefficient_pos (pow_pos hBounds.2.1 3)) hGain

end PrimeFactorOscillations
