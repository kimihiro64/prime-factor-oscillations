/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelParityStability
import PrimeFactorOscillations.Helpers.ThreeLineEffectiveParityThreshold

/-! # An explicit effective parity gap for actual zero clusters -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem zeta_parity_effective_height_gap (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (j : Nat) (hOdd : Odd j) (hEffective : zetaFiniteHorizontalEffectiveMass W = (j : Real))
    (hRange : zetaFiniteHorizontalMomentRatio W <=
      min (1 / 16) (1 / (1024 * threeLineMultiplicityBudget height))) :
    threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
        (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
      threeLineKernelParityCoefficient (zetaFiniteHorizontalMomentRatio W) *
        (zetaFiniteHorizontalMomentRatio W) ^ 3 +
      3 * (zetaFiniteHorizontalMomentRatio W) ^ 3 / threeLineMultiplicityBudget height <
        threeLineCharge * threeLineMultiplicityBudget height := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have hMass : 0 < zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalEffectiveMass
    exact div_pos (sq_pos_of_pos hM) hBounds.1
  have hMassBudget := zeta_effective_mass_le_height_budget height hHeight W hCritical hSame hN hM
  have hBudget : 0 < threeLineMultiplicityBudget height := lt_of_lt_of_le hMass hMassBudget
  have hScale : zetaFiniteHorizontalMomentRatio W <= 1 / 16 :=
    le_trans hRange (min_le_left _ _)
  have hInverse : zetaFiniteHorizontalMomentRatio W <=
      1 / (1024 * threeLineMultiplicityBudget height) :=
    le_trans hRange (min_le_right _ _)
  have hCancel : (1 / (1024 * threeLineMultiplicityBudget height)) *
      (1024 * threeLineMultiplicityBudget height) = 1 := by field_simp [hBudget.ne']
  have hScaledCut := _root_.mul_le_mul_of_nonneg_right hInverse
    (show 0 <= 1024 * threeLineMultiplicityBudget height by linarith)
  have hCutoff : 1024 * threeLineMultiplicityBudget height *
      zetaFiniteHorizontalMomentRatio W <= 1 := by nlinarith only [hCancel, hScaledCut]
  have hMargin := threeLineParityStability_explicit_margin
    (threeLineMultiplicityBudget height) (zetaFiniteHorizontalMomentRatio W) hBudget
    (And.intro (le_of_lt hBounds.2.1) hScale) hCutoff
  have hScaled := _root_.mul_lt_mul_of_pos_left hMargin (pow_pos hBounds.2.1 3)
  have hMain := zeta_parity_stability_odd_height_gap height hHeight W
    hCritical hSame hReflect hN hM j hOdd hEffective
  have hReorder : 3 * (zetaFiniteHorizontalMomentRatio W) ^ 3 /
      threeLineMultiplicityBudget height =
      (zetaFiniteHorizontalMomentRatio W) ^ 3 * (3 / threeLineMultiplicityBudget height) := by ring
  rw [hReorder]
  nlinarith only [hScaled, hMain]

theorem zeta_parity_effective_odd_obstruction (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hRange : zetaFiniteHorizontalMomentRatio W <=
      min (1 / 16) (1 / (1024 * threeLineMultiplicityBudget height)))
    (hCharge : threeLineCharge * threeLineMultiplicityBudget height <=
      threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
        (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
      threeLineKernelParityCoefficient (zetaFiniteHorizontalMomentRatio W) *
        (zetaFiniteHorizontalMomentRatio W) ^ 3 +
      3 * (zetaFiniteHorizontalMomentRatio W) ^ 3 / threeLineMultiplicityBudget height) :
    Not (exists j : Nat, And (Odd j) (zetaFiniteHorizontalEffectiveMass W = (j : Real))) := by
  intro hExists
  choose j hOdd hEffective using hExists
  have hStrict := zeta_parity_effective_height_gap height hHeight W
    hCritical hSame hReflect hN hM j hOdd hEffective hRange
  exact (not_lt_of_ge hCharge) hStrict

end PrimeFactorOscillations
