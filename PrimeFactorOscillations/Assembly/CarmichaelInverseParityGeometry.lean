/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelEffectiveParityThreshold
import PrimeFactorOscillations.Helpers.CompensatedMomentInverseParity

/-! # Joint inverse parity geometry of actual zero clusters -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def zetaParityProfileSlack (height : Real) (W : Finset Complex) : Real :=
  threeLineCharge * threeLineMultiplicityBudget height -
    threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
      (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W)

def zetaParityNormalizedSlack (height : Real) (W : Finset Complex) : Real :=
  zetaParityProfileSlack height W /
    (threeLineParityCubicCoefficient * (zetaFiniteHorizontalMomentRatio W) ^ 3)

def zetaParityNormalizedCoefficient (W : Finset Complex) : Real :=
  threeLineKernelParityCoefficient (zetaFiniteHorizontalMomentRatio W) /
    threeLineParityCubicCoefficient

def zetaParityInverseRadius (height : Real) (W : Finset Complex) : Real :=
  compensatedParityJointRadius (zetaFiniteHorizontalEffectiveMass W)
    (zetaParityNormalizedSlack height W) (zetaParityNormalizedCoefficient W)

theorem zeta_parity_joint_inverse_bound (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (0 <= zetaParityNormalizedSlack height W)
      (And (Even (zetaCompensatedThresholdOrder W))
        (abs (zetaFiniteHorizontalEffectiveMass W - (zetaCompensatedThresholdOrder W : Real)) <=
          zetaParityInverseRadius height W)) := by
  let t := zetaFiniteHorizontalMomentRatio W
  let M := zetaFiniteHorizontalEffectiveMass W
  let D := M - (zetaCompensatedThresholdOrder W : Real)
  let L := zetaParityProfileSlack height W
  let S := zetaParityNormalizedSlack height W
  let c := zetaParityNormalizedCoefficient W
  let scale := threeLineParityCubicCoefficient * t ^ 3
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have htMax := zetaFiniteHorizontalMomentRatio_strip W hCritical hM
  have hTau := threeLineParityCubicCoefficient_pos
  have hC := threeLineKernelParityCoefficient_pos t (le_of_lt hBounds.2.1) htMax
  have hScale : 0 < scale := mul_pos hTau (pow_pos hBounds.2.1 3)
  have hMass : 0 < M := by
    dsimp only [M, zetaFiniteHorizontalEffectiveMass]
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hc : 0 < c := div_pos hC hTau
  have hStrong := zeta_finite_parity_stability_bound height hHeight W
    hCritical hSame hReflect hN hM
  have hCostFull := hStrong.2
  have hKernelFull := (zeta_finite_kernel_parity_bound height hHeight W
    hCritical hSame hReflect hN hM).2
  have hCancel : S * scale = L := by
    dsimp only [S, scale, t, L, zetaParityNormalizedSlack]
    field_simp [hTau.ne', hBounds.2.1.ne']
  have hLinearCancel : c * scale = threeLineKernelParityCoefficient t * t ^ 3 := by
    dsimp only [c, scale, t, zetaParityNormalizedCoefficient]
    field_simp [hTau.ne']
  have hCostCross : scale * compensatedParityStabilityCost M D <= L := by
    dsimp only [scale, t, M, D, L, zetaParityProfileSlack]
    linarith only [hCostFull]
  have hCost : compensatedParityStabilityCost M D <= S := by
    by_contra hNot
    have hProduct := _root_.mul_lt_mul_of_pos_right (lt_of_not_ge hNot) hScale
    nlinarith only [hProduct, hCancel, hCostCross]
  have hCostNonneg : 0 <= compensatedParityStabilityCost M D := by
    rw [compensatedParityStabilityCost_formula]
    exact add_nonneg
      (mul_nonneg (le_of_lt momentRoundThreshold_bounds.1) (abs_nonneg D))
      (div_nonneg
        (mul_nonneg (le_of_lt (sub_pos.mpr momentRoundThreshold_gt_quarter)) (sq_nonneg D))
        (le_of_lt hMass))
  have hSlack : 0 <= S := le_trans hCostNonneg hCost
  have hQuadratic := compensatedParityInverseRadius_bound M D S hMass hSlack hCost
  have hLinearCross : scale * c * abs D <= L := by
    calc
      _ = (c * scale) * abs D := by ring
      _ = threeLineKernelParityCoefficient t * t ^ 3 * abs D := by rw [hLinearCancel]
      _ <= _ := by
        dsimp only [t, D, M, L, zetaParityProfileSlack]
        linarith only [hKernelFull]
  have hLinear : c * abs D <= S := by
    by_contra hNot
    have hProduct := _root_.mul_lt_mul_of_pos_right (lt_of_not_ge hNot) hScale
    nlinarith only [hProduct, hCancel, hLinearCross]
  have hRatioCancel : (S / c) * c = S := by field_simp [hc.ne']
  have hRadius : abs D <= S / c := by
    by_contra hNot
    have hProduct := _root_.mul_lt_mul_of_pos_right (lt_of_not_ge hNot) hc
    nlinarith only [hProduct, hRatioCancel, hLinear]
  exact And.intro hSlack (And.intro hStrong.1 (le_min hQuadratic hRadius))

theorem zeta_parity_inverse_radius_lt_one (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hThreshold : zetaParityNormalizedSlack height W <
      max (zetaParityNormalizedCoefficient W)
        (momentRoundThreshold + (momentRoundThreshold - 1 / 4) /
          zetaFiniteHorizontalEffectiveMass W)) :
    zetaParityInverseRadius height W < 1 := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have htMax := zetaFiniteHorizontalMomentRatio_strip W hCritical hM
  have hMass : 0 < zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalEffectiveMass
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hC := threeLineKernelParityCoefficient_pos _ (le_of_lt hBounds.2.1) htMax
  have hCoefficient : 0 < zetaParityNormalizedCoefficient W :=
    div_pos hC threeLineParityCubicCoefficient_pos
  have hSlack := (zeta_parity_joint_inverse_bound height hHeight W
    hCritical hSame hReflect hN hM).1
  exact compensatedParityJointRadius_lt_one _ _ _ hMass hSlack hCoefficient hThreshold

theorem zeta_parity_inverse_unique_even_order (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hRadius : zetaParityInverseRadius height W < 1) :
    ExistsUnique (fun k : Nat => And (Even k)
      (abs (zetaFiniteHorizontalEffectiveMass W - (k : Real)) <= zetaParityInverseRadius height W)) := by
  have hMain := zeta_parity_joint_inverse_bound height hHeight W
    hCritical hSame hReflect hN hM
  exact evenNatural_unique_in_radius _ _ (zetaCompensatedThresholdOrder W)
    hMain.2.1 hMain.2.2 hRadius

theorem zeta_parity_inverse_threshold_recovery (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hThreshold : zetaParityNormalizedSlack height W <
      max (zetaParityNormalizedCoefficient W)
        (momentRoundThreshold + (momentRoundThreshold - 1 / 4) /
          zetaFiniteHorizontalEffectiveMass W)) :
    ExistsUnique (fun k : Nat => And (Even k)
      (abs (zetaFiniteHorizontalEffectiveMass W - (k : Real)) <= zetaParityInverseRadius height W)) := by
  exact zeta_parity_inverse_unique_even_order height hHeight W
    hCritical hSame hReflect hN hM
    (zeta_parity_inverse_radius_lt_one height hHeight W hCritical hSame hReflect hN hM hThreshold)


theorem zeta_parity_inverse_effective_recovery (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hRange : zetaFiniteHorizontalMomentRatio W <=
      min (1 / 16) (1 / (1024 * threeLineMultiplicityBudget height)))
    (hSlack : zetaParityProfileSlack height W <=
      (threeLineKernelParityCoefficient (zetaFiniteHorizontalMomentRatio W) +
        3 / threeLineMultiplicityBudget height) * (zetaFiniteHorizontalMomentRatio W) ^ 3) :
    ExistsUnique (fun k : Nat => And (Even k)
      (abs (zetaFiniteHorizontalEffectiveMass W - (k : Real)) <= zetaParityInverseRadius height W)) := by
  let t := zetaFiniteHorizontalMomentRatio W
  let B := threeLineMultiplicityBudget height
  let M := zetaFiniteHorizontalEffectiveMass W
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hMass : 0 < M := by
    dsimp only [M, zetaFiniteHorizontalEffectiveMass]
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hMassBudget := zeta_effective_mass_le_height_budget height hHeight W hCritical hSame hN hM
  have hBudget : 0 < B := lt_of_lt_of_le hMass hMassBudget
  have hScale : 0 < threeLineParityCubicCoefficient * t ^ 3 :=
    mul_pos threeLineParityCubicCoefficient_pos (pow_pos hBounds.2.1 3)
  have hSmall : t <= 1 / 16 := le_trans hRange (min_le_left _ _)
  have hInverse : t <= 1 / (1024 * B) := le_trans hRange (min_le_right _ _)
  have hCancelCut : (1 / (1024 * B)) * (1024 * B) = 1 := by field_simp [hBudget.ne']
  have hProduct := _root_.mul_le_mul_of_nonneg_right hInverse
    (show 0 <= 1024 * B by linarith)
  have hCutoff : 1024 * B * t <= 1 := by nlinarith only [hCancelCut, hProduct]
  have hMargin := threeLineParityStability_explicit_margin B t hBudget
    (And.intro (le_of_lt hBounds.2.1) hSmall) hCutoff
  have hScaledMargin := _root_.mul_lt_mul_of_pos_right hMargin (pow_pos hBounds.2.1 3)
  have hRaw : zetaParityProfileSlack height W <
      threeLineParityCubicCoefficient *
        (momentRoundThreshold + (momentRoundThreshold - 1 / 4) / B) * t ^ 3 := by
    nlinarith only [hSlack, hScaledMargin]
  have hCancel : zetaParityNormalizedSlack height W *
      (threeLineParityCubicCoefficient * t ^ 3) = zetaParityProfileSlack height W := by
    dsimp only [zetaParityNormalizedSlack, t]
    field_simp [threeLineParityCubicCoefficient_pos.ne', hBounds.2.1.ne']
  have hNormalized : zetaParityNormalizedSlack height W <
      momentRoundThreshold + (momentRoundThreshold - 1 / 4) / B := by
    by_contra hNot
    have hBad := _root_.mul_le_mul_of_nonneg_right (le_of_not_gt hNot) (le_of_lt hScale)
    nlinarith only [hBad, hCancel, hRaw]
  have hUnit := compensatedParityStabilityCost_unit_budget M B 1 hMass hMassBudget (by norm_num)
  rw [compensatedParityStabilityCost_formula] at hUnit
  norm_num only [abs_one, one_pow, mul_one] at hUnit
  have hThreshold : zetaParityNormalizedSlack height W <
      max (zetaParityNormalizedCoefficient W)
        (momentRoundThreshold + (momentRoundThreshold - 1 / 4) / zetaFiniteHorizontalEffectiveMass W) :=
    lt_of_lt_of_le (lt_of_lt_of_le hNormalized hUnit) (le_max_right _ _)
  exact zeta_parity_inverse_threshold_recovery height hHeight W
    hCritical hSame hReflect hN hM hThreshold

end PrimeFactorOscillations
