/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelMomentRatioMultiplicity
import PrimeFactorOscillations.Helpers.CompensatedMomentRoundingSharpness

/-! # An N-independent compensated parity charge for actual zeta clusters -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

def zetaCompensatedThresholdOrder (W : Finset Complex) : Nat :=
  zetaHorizontalThresholdOrder W
    (2 * momentRoundThreshold * zetaFiniteHorizontalMomentRatio W)

theorem momentRoundIndicator_half (y : Real) :
    momentRoundIndicator momentRoundThreshold y =
      halfRoundIndicator (y / (2 * momentRoundThreshold)) := by
  classical
  have hD := momentRoundThreshold_bounds.1
  have hDen : 0 < 2 * momentRoundThreshold := by positivity
  have hCancel : (y / (2 * momentRoundThreshold)) * (2 * momentRoundThreshold) = y := by
    field_simp [hD.ne']
  unfold momentRoundIndicator halfRoundIndicator
  by_cases hCut : momentRoundThreshold <= y
  case pos =>
    have hHalf : 1 / 2 <= y / (2 * momentRoundThreshold) := by
      by_contra hNot
      have hSmall := lt_of_not_ge hNot
      have hScaled := _root_.mul_lt_mul_of_pos_right hSmall hDen
      nlinarith only [hCancel, hScaled, hCut]
    rw [ite_eq_left hCut, ite_eq_left hHalf]
  case neg =>
    have hHalf : Not (1 / 2 <= y / (2 * momentRoundThreshold)) := by
      intro hLarge
      have hScaled := _root_.mul_le_mul_of_nonneg_right hLarge (le_of_lt hDen)
      have hSmall : y < momentRoundThreshold := lt_of_not_ge hCut
      nlinarith only [hCancel, hScaled, hSmall]
    rw [ite_eq_right hCut, ite_eq_right hHalf]

theorem zetaCompensatedThresholdOrder_cast (W : Finset Complex)
    (ht : 0 < zetaFiniteHorizontalMomentRatio W) :
    (zetaCompensatedThresholdOrder W : Real) =
      Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        momentRoundIndicator momentRoundThreshold
          ((w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W)) := by
  unfold zetaCompensatedThresholdOrder
  rw [zetaHorizontalThresholdOrder_cast]
  apply Finset.sum_congr rfl
  intro w _
  rw [momentRoundIndicator_half]
  have hD := momentRoundThreshold_bounds.1
  have hFraction : ((w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) /
      (2 * momentRoundThreshold) =
        (w.re - 1 / 2) ^ 2 /
          (2 * momentRoundThreshold * zetaFiniteHorizontalMomentRatio W) := by
    field_simp [hD.ne', ht.ne'] <;> ring
  rw [hFraction]

theorem zetaCompensatedThresholdOrder_parity (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w)) :
    And (Even (zetaCompensatedThresholdOrder W))
      (Not (Odd (zetaCompensatedThresholdOrder W))) := by
  exact zetaHorizontalThresholdOrder_parity W
    (2 * momentRoundThreshold * zetaFiniteHorizontalMomentRatio W) hCritical hReflect

theorem zeta_finite_compensated_energy_bound (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    momentRoundThreshold * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      abs (zetaFiniteHorizontalEffectiveMass W - (zetaCompensatedThresholdOrder W : Real)) <=
        Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
          (w.re - 1 / 2) ^ 2 *
            ((w.re - 1 / 2) ^ 2 - zetaFiniteHorizontalMomentRatio W) ^ 2) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have ha : forall w, Membership.mem W w -> 0 <= (analyticOrderNatAt riemannZeta w : Real) :=
    fun _ _ => Nat.cast_nonneg _
  have hx : forall w, Membership.mem W w -> 0 <= (w.re - 1 / 2) ^ 2 :=
    fun w _ => sq_nonneg _
  have hCenter : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2) ^ 2) = zetaFiniteHorizontalMomentRatio W * zetaFiniteHorizontalMoment W := by
    rw [zetaFiniteHorizontalFourthMoment_nested]
    unfold zetaFiniteHorizontalMomentRatio
    field_simp [hM.ne']
  have hRound := finiteWeightedCompensatedRound_scaled W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    (zetaFiniteHorizontalMomentRatio W) hBounds.2.1 ha hx hCenter
  rw [<- zetaCompensatedThresholdOrder_cast W hBounds.2.1] at hRound
  change momentRoundThreshold * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
    abs (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W -
      (zetaCompensatedThresholdOrder W : Real)) <= _ at hRound
  have hEffective : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  rw [hEffective] at hRound
  exact hRound

theorem zeta_finite_compensated_moment_bound (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (Even (zetaCompensatedThresholdOrder W))
      (threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
          (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
        momentRoundThreshold * (zetaFiniteHorizontalMomentRatio W) ^ 3 *
          abs (zetaFiniteHorizontalEffectiveMass W - (zetaCompensatedThresholdOrder W : Real)) <=
            threeLineCharge * threeLineMultiplicityBudget height) := by
  have hBase := zeta_finite_moment_ratio_even_bound height hHeight W
    hCritical hSame hReflect hN hM
  have hEnergy := zeta_finite_compensated_energy_bound W hCritical hN hM
  exact And.intro (zetaCompensatedThresholdOrder_parity W hCritical hReflect).1
    (by nlinarith only [hBase.2.2.1, hEnergy])

theorem odd_even_real_abs_gap (j k : Nat) (hOdd : Odd j) (hNotOdd : Not (Odd k)) :
    1 <= abs ((j : Real) - (k : Real)) := by
  have hNe : Not (j = k) := by
    intro h
    apply hNotOdd
    rw [<- h]
    exact hOdd
  rcases lt_or_gt_of_ne hNe with hLeft | hRight
  case inl =>
    have hNat : j + 1 <= k := Nat.add_one_le_iff.mpr hLeft
    have hReal : (j : Real) + 1 <= (k : Real) := by exact_mod_cast hNat
    have hAbs := neg_le_abs ((j : Real) - (k : Real))
    linarith
  case inr =>
    have hNat : k + 1 <= j := Nat.add_one_le_iff.mpr hRight
    have hReal : (k : Real) + 1 <= (j : Real) := by exact_mod_cast hNat
    have hAbs := le_abs_self ((j : Real) - (k : Real))
    linarith

theorem zeta_compensated_odd_effective_gap (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (j : Nat) (hOdd : Odd j) (hEffective : zetaFiniteHorizontalEffectiveMass W = (j : Real)) :
    threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
        (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
      momentRoundThreshold * (zetaFiniteHorizontalMomentRatio W) ^ 3 <=
        threeLineCharge * threeLineMultiplicityBudget height := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hMain := (zeta_finite_compensated_moment_bound height hHeight W
    hCritical hSame hReflect hN hM).2
  have hGap := odd_even_real_abs_gap j (zetaCompensatedThresholdOrder W) hOdd
    (zetaCompensatedThresholdOrder_parity W hCritical hReflect).2
  rw [<- hEffective] at hGap
  have hCoefficient : 0 <= momentRoundThreshold * (zetaFiniteHorizontalMomentRatio W) ^ 3 :=
    mul_nonneg (le_of_lt momentRoundThreshold_bounds.1)
      (pow_nonneg (le_of_lt hBounds.2.1) 3)
  have hScaled := _root_.mul_le_mul_of_nonneg_left hGap hCoefficient
  nlinarith only [hMain, hScaled]

theorem compensatedParityPenalty_stronger (N t : Real) (hN : 2 <= N) (ht : 0 < t) :
    t ^ 3 / (2 * N) < momentRoundThreshold * t ^ 3 := by
  have hnPos : 0 < N := by linarith
  have hThreshold := momentRoundThreshold_gt_quarter
  have hInverse : (2 * N) * (1 / (2 * N)) = 1 := by field_simp [hnPos.ne']
  have hCoefficient : 1 / (2 * N) < momentRoundThreshold := by
    by_contra hNot
    have hGe : momentRoundThreshold <= 1 / (2 * N) := le_of_not_gt hNot
    have hScaled := _root_.mul_le_mul_of_nonneg_left hGe
      (show 0 <= 2 * N by positivity)
    have hPositive := mul_pos (show 0 < 2 * N by positivity)
      (sub_pos.mpr hThreshold)
    nlinarith only [hInverse, hScaled, hPositive, hN]
  have hScaled := _root_.mul_lt_mul_of_pos_right hCoefficient (pow_pos ht 3)
  calc
    _ = (1 / (2 * N)) * t ^ 3 := by ring
    _ < _ := hScaled

end PrimeFactorOscillations
