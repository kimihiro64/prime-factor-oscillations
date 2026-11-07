/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelHorizontalMultiplicity
import PrimeFactorOscillations.Helpers.XiClusterMultiplicity

/-! # Unconditional anisotropic multiplicity budgets on physical height intervals -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

def zetaClusterVerticalMoment (T : Real) (W : Finset Complex) : Real :=
  Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) * (T - w.im) ^ 2)

def threeLineClusterWindowConstant : Real :=
  threeLineCharge / (threeLineCharge - 3 / 16) * threeLineMultiplicityConstant

theorem zeta_finite_cluster_budget_unscaled (T : Real) (hT : 2 <= abs T)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1)) :
    threeLineCharge * zetaFiniteMultiplicityMass W +
      (13 / 2 : Real) * zetaFiniteHorizontalMoment W -
        48 * zetaClusterVerticalMoment T W <= threeLineCharge * threeLineMultiplicityBudget T := by
  have h := (zeta_finite_cluster_charge_trace T W hCritical
    xi_seven_eighths_centered_strip).trans (xi_threeLine_trace_upper T hT)
  have hMass : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      (threeLineCharge + (13 / 2 : Real) * (w.re - 1 / 2) ^ 2 - 48 * (T - w.im) ^ 2)) =
      threeLineCharge * zetaFiniteMultiplicityMass W +
        (13 / 2 : Real) * zetaFiniteHorizontalMoment W -
          48 * zetaClusterVerticalMoment T W := by
    unfold zetaFiniteMultiplicityMass zetaFiniteHorizontalMoment zetaClusterVerticalMoment
    calc
      _ = Finset.sum W (fun w => threeLineCharge * (analyticOrderNatAt riemannZeta w : Real) +
          (13 / 2 : Real) * ((analyticOrderNatAt riemannZeta w : Real) * (w.re - 1 / 2) ^ 2) -
            48 * ((analyticOrderNatAt riemannZeta w : Real) * (T - w.im) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          <- Finset.mul_sum, <- Finset.mul_sum, <- Finset.mul_sum]
  have hUpper : (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) / 2 *
      Real.log (abs T) + (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) *
        threeLineHeightConstant + threeLineLipschitzConstant * threeLineRemainderScale =
      threeLineCharge * threeLineMultiplicityBudget T := by
    unfold threeLineMultiplicityBudget threeLineLeadingCoefficient threeLineMultiplicityConstant
    field_simp [threeLineCharge_pos.ne'] <;> ring
  rw [hMass, hUpper] at h
  exact h

theorem zeta_finite_cluster_budget (T : Real) (hT : 2 <= abs T) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1)) :
    zetaFiniteMultiplicityMass W + (13 / (2 * threeLineCharge) : Real) *
      zetaFiniteHorizontalMoment W - (48 / threeLineCharge : Real) *
        zetaClusterVerticalMoment T W <= threeLineMultiplicityBudget T := by
  have h := zeta_finite_cluster_budget_unscaled T hT W hCritical
  have he : threeLineCharge * (zetaFiniteMultiplicityMass W +
      (13 / (2 * threeLineCharge) : Real) * zetaFiniteHorizontalMoment W -
        (48 / threeLineCharge : Real) * zetaClusterVerticalMoment T W) =
      threeLineCharge * zetaFiniteMultiplicityMass W +
        (13 / 2 : Real) * zetaFiniteHorizontalMoment W -
          48 * zetaClusterVerticalMoment T W := by
    field_simp [threeLineCharge_pos.ne'] <;> ring
  rw [<- he] at h
  exact (_root_.mul_le_mul_iff_of_pos_left threeLineCharge_pos).mp h

theorem zeta_finite_cluster_rigidity (T : Real) (hT : 2 <= abs T) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (eta : Real)
    (hNear : (1 - eta) * threeLineMultiplicityBudget T <= zetaFiniteMultiplicityMass W) :
    (13 / (2 * threeLineCharge) : Real) * zetaFiniteHorizontalMoment W <=
      eta * threeLineMultiplicityBudget T +
        (48 / threeLineCharge : Real) * zetaClusterVerticalMoment T W := by
  have h := zeta_finite_cluster_budget T hT W hCritical
  nlinarith only [h, hNear]

theorem zetaClusterVerticalMoment_le_window (T h : Real) (W : Finset Complex)
    (hWindow : forall w, Membership.mem W w -> abs (T - w.im) <= h) :
    zetaClusterVerticalMoment T W <= h ^ 2 * zetaFiniteMultiplicityMass W := by
  unfold zetaClusterVerticalMoment zetaFiniteMultiplicityMass
  calc
    _ <= Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) * h ^ 2) := by
      apply Finset.sum_le_sum
      intro w hw
      have hab := abs_le.mp (hWindow w hw)
      have hm : 0 <= (h - (T - w.im)) * (h + (T - w.im)) :=
        mul_nonneg (by linarith only [hab.2]) (by linarith only [hab.1])
      have hs : (T - w.im) ^ 2 <= h ^ 2 := by nlinarith only [hm]
      exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring

theorem zeta_finite_cluster_window_charge (T : Real) (hT : 2 <= abs T)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (h : Real) (hWindow : forall w, Membership.mem W w -> abs (T - w.im) <= h) :
    (threeLineCharge - 48 * h ^ 2) * zetaFiniteMultiplicityMass W +
      (13 / 2 : Real) * zetaFiniteHorizontalMoment W <=
        threeLineCharge * threeLineMultiplicityBudget T := by
  have hJoint := zeta_finite_cluster_budget_unscaled T hT W hCritical
  have hMoment := zetaClusterVerticalMoment_le_window T h W hWindow
  nlinarith only [hJoint, hMoment]

theorem zeta_finite_cluster_window_count (T : Real) (hT : 2 <= abs T)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (h : Real) (hSmall : 48 * h ^ 2 < threeLineCharge)
    (hWindow : forall w, Membership.mem W w -> abs (T - w.im) <= h) :
    zetaFiniteMultiplicityMass W <=
      threeLineCharge / (threeLineCharge - 48 * h ^ 2) * threeLineMultiplicityBudget T := by
  have hJoint := zeta_finite_cluster_window_charge T hT W hCritical h hWindow
  have hMoment := zetaFiniteHorizontalMoment_nonneg W
  have hCount : (threeLineCharge - 48 * h ^ 2) * zetaFiniteMultiplicityMass W <=
      threeLineCharge * threeLineMultiplicityBudget T := by linarith only [hJoint, hMoment]
  have hd : 0 < threeLineCharge - 48 * h ^ 2 := sub_pos.mpr hSmall
  have he : (threeLineCharge - 48 * h ^ 2) *
      (threeLineCharge / (threeLineCharge - 48 * h ^ 2) * threeLineMultiplicityBudget T) =
      threeLineCharge * threeLineMultiplicityBudget T := by
    field_simp [hd.ne'] <;> ring
  rw [<- he] at hCount
  exact (_root_.mul_le_mul_iff_of_pos_left hd).mp hCount

theorem threeLineClusterWindowConstant_nonneg : 0 <= threeLineClusterWindowConstant := by
  unfold threeLineClusterWindowConstant
  exact mul_nonneg (div_nonneg threeLineCharge_pos.le (by norm_num [threeLineCharge]))
    threeLineMultiplicityConstant_nonneg

theorem zeta_finite_cluster_one_sixteenth_window (T : Real) (hT : 2 <= abs T)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hWindow : forall w, Membership.mem W w -> abs (T - w.im) <= 1 / 16) :
    zetaFiniteMultiplicityMass W <=
      (4625194854 / 28457195785 : Real) * Real.log (abs T) +
        threeLineClusterWindowConstant := by
  have h := zeta_finite_cluster_window_count T hT W hCritical (1 / 16)
    (by norm_num [threeLineCharge]) hWindow
  convert h using 1
  unfold threeLineMultiplicityBudget threeLineClusterWindowConstant
  rw [threeLineLeadingCoefficient_eq]
  norm_num [threeLineCharge] <;> ring

end PrimeFactorOscillations
