/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNonlinearThreshold
import PrimeFactorOscillations.Helpers.NegativeThresholdTransport
import PrimeFactorOscillations.Helpers.ThresholdFixedTotalSharpness
import PrimeFactorOscillations.Helpers.ThresholdTransportStability

/-! # Lipschitz profile stability from the complete signed zero-cluster budget -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem zeta_finite_threshold_transport_tilt (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hKM : (zetaCompensatedThresholdOrder W : Real) <= zetaFiniteHorizontalEffectiveMass W)
    (l : Real) (phi : Real -> Real)
    (hl : And (0 <= l) (l <= thresholdBandSlope momentRoundThreshold
      (thresholdPositiveRoot momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
        (zetaCompensatedThresholdOrder W : Real))))
    (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    let t := zetaFiniteHorizontalMomentRatio W
    let M := zetaFiniteHorizontalEffectiveMass W
    let K := (zetaCompensatedThresholdOrder W : Real)
    let N := zetaFiniteMultiplicityMass W
    let d := momentRoundThreshold
    let z := thresholdPositiveRoot d M K
    l * abs (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        phi (((w.re - 1 / 2) ^ 2) / t)) - thresholdCanonicalStatistic d z M K N phi) <=
      2 * ((threeLineCharge * threeLineMultiplicityBudget height -
        threeLineMomentRatioCharge N (zetaFiniteHorizontalMoment W)
          (zetaFiniteHorizontalFourthMoment W)) / (threeLineParityCubicCoefficient * t ^ 3) -
        thresholdPositiveCost d M K) +
        K * l ^ 2 / (2 * thresholdBandCurvature d z) := by
  dsimp only
  let t := zetaFiniteHorizontalMomentRatio W
  let M := zetaFiniteHorizontalEffectiveMass W
  let K := (zetaCompensatedThresholdOrder W : Real)
  let N := zetaFiniteMultiplicityMass W
  let d := momentRoundThreshold
  let z := thresholdPositiveRoot d M K
  let a := fun w : Complex => (analyticOrderNatAt riemannZeta w : Real)
  let x := fun w : Complex => (w.re - 1 / 2) ^ 2
  let y := fun w : Complex => x w / t
  let E := Finset.sum W (fun w => a w * y w * (y w - 1) ^ 2)
  let p := threeLineParityCubicCoefficient * t ^ 3
  let B2 := threeLineMomentRatioCharge N (zetaFiniteHorizontalMoment W)
    (zetaFiniteHorizontalFourthMoment W)
  let gB := threeLineCharge * threeLineMultiplicityBudget height
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have ht : 0 < t := hBounds.2.1
  have htMax : t <= 9 / 64 := zetaFiniteHorizontalMomentRatio_strip W hCritical hM
  have hd : And (0 < d) (d < 1) :=
    And.intro momentRoundThreshold_bounds.1 (by have hh := momentRoundThreshold_bounds.2; linarith)
  have ha : forall w, Membership.mem W w -> 0 <= a w := fun _ _ => Nat.cast_nonneg _
  have hx : forall w, Membership.mem W w -> And (0 <= x w) (x w <= 1 / 4) :=
    fun w hw => zeta_horizontal_square_bounds w (hCritical w hw)
  have hCenter : Finset.sum W (fun w => a w * (x w) ^ 2) =
      t * Finset.sum W (fun w => a w * x w) := by
    change Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2) ^ 2) =
        zetaFiniteHorizontalMomentRatio W * zetaFiniteHorizontalMoment W
    rw [zetaFiniteHorizontalFourthMoment_nested]
    unfold zetaFiniteHorizontalMomentRatio
    field_simp [hM.ne']
  have hNormMoment : Finset.sum W (fun w => a w * (y w) ^ 2) =
      Finset.sum W (fun w => a w * y w) := by
    calc
      _ = Finset.sum W (fun w => a w * (x w) ^ 2) / t ^ 2 := by
        dsimp [y]
        simp only [div_pow]
        exact finiteWeighted_div_sum W a (fun w => (x w) ^ 2) (t ^ 2)
      _ = Finset.sum W (fun w => a w * x w) / t := by
        rw [hCenter]
        field_simp [ht.ne']
      _ = _ := (finiteWeighted_div_sum W a x t).symm
  have hNormMass : Finset.sum W (fun w => a w * y w) = M := by
    dsimp [y]
    rw [finiteWeighted_div_sum]
    change zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  have hNormK : thresholdSelectedMass d W a y = K := by
    unfold thresholdSelectedMass
    exact (zetaCompensatedThresholdOrder_cast W ht).symm
  have hKappa : 0 < M := by
    dsimp [M, zetaFiniteHorizontalEffectiveMass]
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hPositive : 0 < Finset.sum W (fun w => a w * y w) := by
    rw [hNormMass]
    exact hKappa
  have hNormKM : thresholdSelectedMass d W a y <= Finset.sum W (fun w => a w * y w) := by
    rw [hNormK, hNormMass]
    exact hKM
  have hTilt := finiteWeightedThreshold_lipschitz_stability W a y d l phi hd ha
    (fun w hw => div_nonneg (hx w hw).1 ht.le) hNormMoment hPositive hNormKM
    (by simpa only [hNormMass, hNormK] using hl) hphi
  rw [hNormMass, hNormK] at hTilt
  change l * abs (Finset.sum W (fun w => a w * phi (y w)) -
      thresholdCanonicalStatistic d z M K N phi) <=
        2 * (E - thresholdPositiveCost d M K) + K * l ^ 2 / (2 * thresholdBandCurvature d z) at hTilt
  have hEnergy : t ^ 3 * E = Finset.sum W (fun w => a w * x w * (x w - t) ^ 2) := by
    dsimp [E, y]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    have hh := congrArg (fun q : Real => a w * q) (finiteWeighted_rescale_energy (x w) t ht)
    nlinarith only [hh]
  have hFloor : threeLineParityCubicCoefficient *
      Finset.sum W (fun w => a w * x w * (x w - t) ^ 2) <=
      Finset.sum W (fun w => a w * x w * (x w - t) ^ 2 *
        threeLineSizeBiasedRemainder (x w) t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w hw
    have hKernel := threeLineSizeBiasedRemainder_ge_tau (x w) t (hx w hw).1 (hx w hw).2 ht.le htMax
    have hNonneg : 0 <= a w * x w * (x w - t) ^ 2 :=
      mul_nonneg (mul_nonneg (ha w hw) (hx w hw).1) (sq_nonneg _)
    have hh := _root_.mul_le_mul_of_nonneg_left hKernel hNonneg
    nlinarith only [hh]
  have hLedger := threeLineWeightedKernel_ledger W a x t (by linarith only [htMax])
    (fun w hw => (hx w hw).2) hCenter
  change Finset.sum W (fun w => a w * threeLineHorizontalProfile (x w)) =
    threeLineCharge * N + threeLineSizeBiasedProfile t * Finset.sum W (fun w => a w * x w) +
      Finset.sum W (fun w => a w * x w * (x w - t) ^ 2 *
        threeLineSizeBiasedRemainder (x w) t) at hLedger
  have hUpper := zeta_finite_horizontal_profile_upper height hHeight W hCritical hSame
  have hCharge : B2 = threeLineCharge * N +
      threeLineSizeBiasedProfile t * Finset.sum W (fun w => a w * x w) := by
    change threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
      (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) =
        threeLineCharge * zetaFiniteMultiplicityMass W +
          threeLineSizeBiasedProfile (zetaFiniteHorizontalMomentRatio W) * zetaFiniteHorizontalMoment W
    unfold threeLineMomentRatioCharge zetaFiniteHorizontalMomentRatio
    ring
  have hScaled := congrArg (fun q : Real => threeLineParityCubicCoefficient * q) hEnergy
  have hBudget : B2 + p * E <= gB := by
    change B2 + (threeLineParityCubicCoefficient * t ^ 3) * E <= gB
    change Finset.sum W (fun w => a w * threeLineHorizontalProfile (x w)) <= gB at hUpper
    nlinarith only [hFloor, hLedger, hUpper, hCharge, hScaled]
  have hp : 0 < p := mul_pos threeLineParityCubicCoefficient_pos (pow_pos ht 3)
  have hDiv : p * ((gB - B2) / p) = gB - B2 := by field_simp [hp.ne']
  have hE : E <= (gB - B2) / p := by
    by_contra hn
    have hP := mul_pos hp (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hBudget, hDiv, hP]
  change l * abs (Finset.sum W (fun w => a w * phi (y w)) -
      thresholdCanonicalStatistic d z M K N phi) <=
        2 * ((gB - B2) / p - thresholdPositiveCost d M K) +
          K * l ^ 2 / (2 * thresholdBandCurvature d z)
  nlinarith only [hTilt, hE]

theorem zeta_finite_negative_threshold_transport_tilt (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hMK : zetaFiniteHorizontalEffectiveMass W < (zetaCompensatedThresholdOrder W : Real))
    (l : Real) (phi : Real -> Real)
    (hl : And (0 <= l) (l <= negativeThresholdSlope momentRoundThreshold
      (thresholdNegativeRoot momentRoundThreshold (zetaFiniteHorizontalEffectiveMass W)
        (zetaCompensatedThresholdOrder W : Real))))
    (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    let t := zetaFiniteHorizontalMomentRatio W
    let M := zetaFiniteHorizontalEffectiveMass W
    let K := (zetaCompensatedThresholdOrder W : Real)
    let N := zetaFiniteMultiplicityMass W
    let d := momentRoundThreshold
    let z := thresholdNegativeRoot d M K
    l * abs (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        phi (((w.re - 1 / 2) ^ 2) / t)) - negativeThresholdCanonicalStatistic d z M K N phi) <=
      2 * ((threeLineCharge * threeLineMultiplicityBudget height -
        threeLineMomentRatioCharge N (zetaFiniteHorizontalMoment W)
          (zetaFiniteHorizontalFourthMoment W)) / (threeLineParityCubicCoefficient * t ^ 3) -
        thresholdNegativeCost d M K) +
        K * l ^ 2 / (2 * negativeThresholdCurvature d z) := by
  dsimp only
  let t := zetaFiniteHorizontalMomentRatio W
  let M := zetaFiniteHorizontalEffectiveMass W
  let K := (zetaCompensatedThresholdOrder W : Real)
  let N := zetaFiniteMultiplicityMass W
  let d := momentRoundThreshold
  let z := thresholdNegativeRoot d M K
  let a := fun w : Complex => (analyticOrderNatAt riemannZeta w : Real)
  let x := fun w : Complex => (w.re - 1 / 2) ^ 2
  let y := fun w : Complex => x w / t
  let E := Finset.sum W (fun w => a w * y w * (y w - 1) ^ 2)
  let p := threeLineParityCubicCoefficient * t ^ 3
  let B2 := threeLineMomentRatioCharge N (zetaFiniteHorizontalMoment W)
    (zetaFiniteHorizontalFourthMoment W)
  let gB := threeLineCharge * threeLineMultiplicityBudget height
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have ht : 0 < t := hBounds.2.1
  have htMax : t <= 9 / 64 := zetaFiniteHorizontalMomentRatio_strip W hCritical hM
  have hd : And (0 < d) (d < 1) :=
    And.intro momentRoundThreshold_bounds.1 (by have hh := momentRoundThreshold_bounds.2; linarith)
  have ha : forall w, Membership.mem W w -> 0 <= a w := fun _ _ => Nat.cast_nonneg _
  have hx : forall w, Membership.mem W w -> And (0 <= x w) (x w <= 1 / 4) :=
    fun w hw => zeta_horizontal_square_bounds w (hCritical w hw)
  have hCenter : Finset.sum W (fun w => a w * (x w) ^ 2) =
      t * Finset.sum W (fun w => a w * x w) := by
    change Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2) ^ 2) =
        zetaFiniteHorizontalMomentRatio W * zetaFiniteHorizontalMoment W
    rw [zetaFiniteHorizontalFourthMoment_nested]
    unfold zetaFiniteHorizontalMomentRatio
    field_simp [hM.ne']
  have hNormMoment : Finset.sum W (fun w => a w * (y w) ^ 2) =
      Finset.sum W (fun w => a w * y w) := by
    calc
      _ = Finset.sum W (fun w => a w * (x w) ^ 2) / t ^ 2 := by
        dsimp [y]
        simp only [div_pow]
        exact finiteWeighted_div_sum W a (fun w => (x w) ^ 2) (t ^ 2)
      _ = Finset.sum W (fun w => a w * x w) / t := by
        rw [hCenter]
        field_simp [ht.ne']
      _ = _ := (finiteWeighted_div_sum W a x t).symm
  have hNormMass : Finset.sum W (fun w => a w * y w) = M := by
    dsimp [y]
    rw [finiteWeighted_div_sum]
    change zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  have hNormK : thresholdSelectedMass d W a y = K := by
    unfold thresholdSelectedMass
    exact (zetaCompensatedThresholdOrder_cast W ht).symm
  have hKappa : 0 < M := by
    dsimp [M, zetaFiniteHorizontalEffectiveMass]
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hPositive : 0 < Finset.sum W (fun w => a w * y w) := by
    rw [hNormMass]
    exact hKappa
  have hNormMK : Finset.sum W (fun w => a w * y w) < thresholdSelectedMass d W a y := by
    rw [hNormK, hNormMass]
    exact hMK
  have hTilt := finiteWeightedNegative_lipschitz_stability W a y d l phi hd ha
    (fun w hw => div_nonneg (hx w hw).1 ht.le) hNormMoment hPositive hNormMK
    (by simpa only [hNormMass, hNormK] using hl) hphi
  rw [hNormMass, hNormK] at hTilt
  change l * abs (Finset.sum W (fun w => a w * phi (y w)) -
      negativeThresholdCanonicalStatistic d z M K N phi) <=
        2 * (E - thresholdNegativeCost d M K) + K * l ^ 2 / (2 * negativeThresholdCurvature d z) at hTilt
  have hEnergy : t ^ 3 * E = Finset.sum W (fun w => a w * x w * (x w - t) ^ 2) := by
    dsimp [E, y]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    have hh := congrArg (fun q : Real => a w * q) (finiteWeighted_rescale_energy (x w) t ht)
    nlinarith only [hh]
  have hFloor : threeLineParityCubicCoefficient *
      Finset.sum W (fun w => a w * x w * (x w - t) ^ 2) <=
      Finset.sum W (fun w => a w * x w * (x w - t) ^ 2 *
        threeLineSizeBiasedRemainder (x w) t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w hw
    have hKernel := threeLineSizeBiasedRemainder_ge_tau (x w) t (hx w hw).1 (hx w hw).2 ht.le htMax
    have hNonneg : 0 <= a w * x w * (x w - t) ^ 2 :=
      mul_nonneg (mul_nonneg (ha w hw) (hx w hw).1) (sq_nonneg _)
    have hh := _root_.mul_le_mul_of_nonneg_left hKernel hNonneg
    nlinarith only [hh]
  have hLedger := threeLineWeightedKernel_ledger W a x t (by linarith only [htMax])
    (fun w hw => (hx w hw).2) hCenter
  change Finset.sum W (fun w => a w * threeLineHorizontalProfile (x w)) =
    threeLineCharge * N + threeLineSizeBiasedProfile t * Finset.sum W (fun w => a w * x w) +
      Finset.sum W (fun w => a w * x w * (x w - t) ^ 2 *
        threeLineSizeBiasedRemainder (x w) t) at hLedger
  have hUpper := zeta_finite_horizontal_profile_upper height hHeight W hCritical hSame
  have hCharge : B2 = threeLineCharge * N +
      threeLineSizeBiasedProfile t * Finset.sum W (fun w => a w * x w) := by
    change threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
      (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) =
        threeLineCharge * zetaFiniteMultiplicityMass W +
          threeLineSizeBiasedProfile (zetaFiniteHorizontalMomentRatio W) * zetaFiniteHorizontalMoment W
    unfold threeLineMomentRatioCharge zetaFiniteHorizontalMomentRatio
    ring
  have hScaled := congrArg (fun q : Real => threeLineParityCubicCoefficient * q) hEnergy
  have hBudget : B2 + p * E <= gB := by
    change B2 + (threeLineParityCubicCoefficient * t ^ 3) * E <= gB
    change Finset.sum W (fun w => a w * threeLineHorizontalProfile (x w)) <= gB at hUpper
    nlinarith only [hFloor, hLedger, hUpper, hCharge, hScaled]
  have hp : 0 < p := mul_pos threeLineParityCubicCoefficient_pos (pow_pos ht 3)
  have hDiv : p * ((gB - B2) / p) = gB - B2 := by field_simp [hp.ne']
  have hE : E <= (gB - B2) / p := by
    by_contra hn
    have hP := mul_pos hp (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hBudget, hDiv, hP]
  change l * abs (Finset.sum W (fun w => a w * phi (y w)) -
      negativeThresholdCanonicalStatistic d z M K N phi) <=
        2 * ((gB - B2) / p - thresholdNegativeCost d M K) +
          K * l ^ 2 / (2 * negativeThresholdCurvature d z)
  nlinarith only [hTilt, hE]

end PrimeFactorOscillations
