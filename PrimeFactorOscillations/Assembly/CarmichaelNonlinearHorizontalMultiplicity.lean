/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelHorizontalMultiplicity
import PrimeFactorOscillations.Helpers.XiNonlinearHorizontalMultiplicity

/-! # Unconditional nonlinear zero-cluster geometry and a positive fourth-moment charge -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

def zetaFiniteHorizontalMean (W : Finset Complex) : Real :=
  zetaFiniteHorizontalMoment W / zetaFiniteMultiplicityMass W

def zetaFiniteHorizontalVariance (W : Finset Complex) (z : Real) : Real :=
  Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
    ((w.re - 1 / 2) ^ 2 - z) ^ 2)

def zetaFiniteHorizontalFourthMoment (W : Finset Complex) : Real :=
  Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) * (w.re - 1 / 2) ^ 4)

theorem zetaFiniteHorizontalVariance_nonneg (W : Finset Complex) (z : Real) :
    0 <= zetaFiniteHorizontalVariance W z := by
  apply Finset.sum_nonneg
  intro w _
  exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem zetaFiniteHorizontalFourthMoment_nonneg (W : Finset Complex) :
    0 <= zetaFiniteHorizontalFourthMoment W := by
  apply Finset.sum_nonneg
  intro w _
  positivity

theorem zetaFiniteHorizontalMean_balance (W : Finset Complex)
    (hN : 0 < zetaFiniteMultiplicityMass W) :
    zetaFiniteHorizontalMoment W =
      zetaFiniteMultiplicityMass W * zetaFiniteHorizontalMean W := by
  unfold zetaFiniteHorizontalMean
  field_simp [ne_of_gt hN]

theorem zetaFiniteHorizontalVariance_identity (W : Finset Complex) (z : Real) :
    zetaFiniteHorizontalVariance W z = zetaFiniteHorizontalFourthMoment W -
      2 * z * zetaFiniteHorizontalMoment W + z ^ 2 * zetaFiniteMultiplicityMass W := by
  unfold zetaFiniteHorizontalVariance zetaFiniteHorizontalFourthMoment
    zetaFiniteHorizontalMoment zetaFiniteMultiplicityMass
  calc
    _ = Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        (w.re - 1 / 2) ^ 4 - 2 * z *
          ((analyticOrderNatAt riemannZeta w : Real) * (w.re - 1 / 2) ^ 2) +
            z ^ 2 * (analyticOrderNatAt riemannZeta w : Real)) := by
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum,
        <- Finset.mul_sum]

theorem zeta_finite_horizontal_nonlinear_budget (t : Real) (ht : 2 <= abs t)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t)
    (hN : 0 < zetaFiniteMultiplicityMass W) :
    And (And (0 <= zetaFiniteHorizontalMean W) (zetaFiniteHorizontalMean W <= 9 / 64))
      (zetaFiniteMultiplicityMass W * threeLineHorizontalProfile (zetaFiniteHorizontalMean W) +
        threeLineHorizontalVarianceCoefficient *
          zetaFiniteHorizontalVariance W (zetaFiniteHorizontalMean W) <=
            threeLineCharge * threeLineMultiplicityBudget t) := by
  have h := zeta_finite_horizontal_nonlinear_charge_trace t W hCritical hSame
    xi_seven_eighths_centered_strip (zetaFiniteHorizontalMean W) hN
      (zetaFiniteHorizontalMean_balance W hN)
  have hUpper := xi_threeLine_trace_upper t ht
  have hUpperEq : (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) / 2 *
      Real.log (abs t) + (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) *
        threeLineHeightConstant + threeLineLipschitzConstant * threeLineRemainderScale =
      threeLineCharge * threeLineMultiplicityBudget t := by
    unfold threeLineMultiplicityBudget threeLineLeadingCoefficient threeLineMultiplicityConstant
    field_simp [threeLineCharge_pos.ne']
    ring
  rw [hUpperEq] at hUpper
  exact And.intro h.1 (h.2.trans hUpper)

theorem zeta_horizontal_joint_charge_dominates_quartic (W : Finset Complex)
    (hN : 0 < zetaFiniteMultiplicityMass W)
    (hMean : And (0 <= zetaFiniteHorizontalMean W) (zetaFiniteHorizontalMean W <= 9 / 64)) :
    threeLineCharge * zetaFiniteMultiplicityMass W +
      threeLineHorizontalSlope 0 * zetaFiniteHorizontalMoment W +
        threeLineHorizontalVarianceCoefficient * zetaFiniteHorizontalFourthMoment W <=
      zetaFiniteMultiplicityMass W * threeLineHorizontalProfile (zetaFiniteHorizontalMean W) +
        threeLineHorizontalVarianceCoefficient *
          zetaFiniteHorizontalVariance W (zetaFiniteHorizontalMean W) := by
  have hPhi := threeLineHorizontal_quartic_charge (zetaFiniteHorizontalMean W) hMean
  have hMul := _root_.mul_le_mul_of_nonneg_left hPhi (le_of_lt hN)
  have hBalance := zetaFiniteHorizontalMean_balance W hN
  have hVariance := zetaFiniteHorizontalVariance_identity W (zetaFiniteHorizontalMean W)
  have hAlg : threeLineCharge * zetaFiniteMultiplicityMass W +
      threeLineHorizontalSlope 0 * zetaFiniteHorizontalMoment W +
        threeLineHorizontalVarianceCoefficient * zetaFiniteHorizontalFourthMoment W =
      zetaFiniteMultiplicityMass W * (threeLineCharge +
        threeLineHorizontalSlope 0 * zetaFiniteHorizontalMean W +
          threeLineHorizontalVarianceCoefficient * (zetaFiniteHorizontalMean W) ^ 2) +
        threeLineHorizontalVarianceCoefficient *
          zetaFiniteHorizontalVariance W (zetaFiniteHorizontalMean W) := by
    rw [hVariance, hBalance]
    ring
  exact hAlg.le.trans (_root_.add_le_add hMul (le_refl _))

theorem zeta_finite_horizontal_quartic_budget (t : Real) (ht : 2 <= abs t)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t)
    (hN : 0 < zetaFiniteMultiplicityMass W) :
    threeLineCharge * zetaFiniteMultiplicityMass W +
      threeLineHorizontalSlope 0 * zetaFiniteHorizontalMoment W +
        threeLineHorizontalVarianceCoefficient * zetaFiniteHorizontalFourthMoment W <=
      threeLineCharge * threeLineMultiplicityBudget t := by
  have h := zeta_finite_horizontal_nonlinear_budget t ht W hCritical hSame hN
  exact (zeta_horizontal_joint_charge_dominates_quartic W hN h.1).trans h.2

theorem zeta_horizontal_quartic_charge_dominates_old (W : Finset Complex) :
    threeLineCharge * zetaFiniteMultiplicityMass W +
      (13 / 2 : Real) * zetaFiniteHorizontalMoment W <=
        threeLineCharge * zetaFiniteMultiplicityMass W +
          threeLineHorizontalSlope 0 * zetaFiniteHorizontalMoment W +
            threeLineHorizontalVarianceCoefficient * zetaFiniteHorizontalFourthMoment W := by
  have hM := zetaFiniteHorizontalMoment_nonneg W
  have hQ := zetaFiniteHorizontalFourthMoment_nonneg W
  have hSlope := threeLineHorizontalSlope_zero_gt
  have hSigma := threeLineHorizontalVarianceCoefficient_pos
  have h1 := mul_nonneg (le_of_lt (sub_pos.mpr hSlope)) hM
  have h2 := mul_nonneg (le_of_lt hSigma) hQ
  nlinarith

theorem zeta_horizontal_quartic_charge_strict (W : Finset Complex)
    (hM : 0 < zetaFiniteHorizontalMoment W) :
    threeLineCharge * zetaFiniteMultiplicityMass W +
      (13 / 2 : Real) * zetaFiniteHorizontalMoment W <
        threeLineCharge * zetaFiniteMultiplicityMass W +
          threeLineHorizontalSlope 0 * zetaFiniteHorizontalMoment W +
            threeLineHorizontalVarianceCoefficient * zetaFiniteHorizontalFourthMoment W := by
  have hQ := zetaFiniteHorizontalFourthMoment_nonneg W
  have h1 := mul_pos (sub_pos.mpr threeLineHorizontalSlope_zero_gt) hM
  have h2 := mul_nonneg (le_of_lt threeLineHorizontalVarianceCoefficient_pos) hQ
  nlinarith

end PrimeFactorOscillations
