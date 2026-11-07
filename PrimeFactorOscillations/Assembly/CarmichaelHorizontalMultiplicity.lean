/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelThreeLineMultiplicity
import PrimeFactorOscillations.Helpers.XiHorizontalMultiplicity

/-! # Unconditional common-ordinate multiplicity and horizontal rigidity -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

def zetaFiniteMultiplicityMass (W : Finset Complex) : Real :=
  Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real))

def zetaFiniteHorizontalMoment (W : Finset Complex) : Real :=
  Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) * (w.re - 1 / 2) ^ 2)

def threeLineMultiplicityBudget (t : Real) : Real :=
  threeLineLeadingCoefficient * Real.log (abs t) + threeLineMultiplicityConstant

theorem zetaFiniteHorizontalMoment_nonneg (W : Finset Complex) :
    0 <= zetaFiniteHorizontalMoment W := by
  apply Finset.sum_nonneg
  intro w _
  exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem zeta_finite_horizontal_budget (t : Real) (ht : 2 <= abs t) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t) :
    threeLineCharge * zetaFiniteMultiplicityMass W +
      (13 / 2 : Real) * zetaFiniteHorizontalMoment W <=
        threeLineCharge * threeLineMultiplicityBudget t := by
  have h := (zeta_finite_horizontal_charge_trace t W hCritical hSame
    xi_seven_eighths_centered_strip).trans (xi_threeLine_trace_upper t ht)
  have hMass : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      (threeLineCharge + (13 / 2 : Real) * (w.re - 1 / 2) ^ 2)) =
      threeLineCharge * zetaFiniteMultiplicityMass W +
        (13 / 2 : Real) * zetaFiniteHorizontalMoment W := by
    unfold zetaFiniteMultiplicityMass zetaFiniteHorizontalMoment
    calc
      _ = Finset.sum W (fun w => threeLineCharge * (analyticOrderNatAt riemannZeta w : Real) +
          (13 / 2 : Real) * ((analyticOrderNatAt riemannZeta w : Real) * (w.re - 1 / 2) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
  have hUpper : (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) / 2 *
      Real.log (abs t) + (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) *
        threeLineHeightConstant + threeLineLipschitzConstant * threeLineRemainderScale =
      threeLineCharge * threeLineMultiplicityBudget t := by
    unfold threeLineMultiplicityBudget threeLineLeadingCoefficient threeLineMultiplicityConstant
    field_simp [threeLineCharge_pos.ne']
    ring
  rw [hMass, hUpper] at h
  exact h

theorem zeta_finite_horizontal_budget_normalized (t : Real) (ht : 2 <= abs t)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t) :
    zetaFiniteMultiplicityMass W + (13 / (2 * threeLineCharge) : Real) *
      zetaFiniteHorizontalMoment W <= threeLineMultiplicityBudget t := by
  have h := zeta_finite_horizontal_budget t ht W hCritical hSame
  have he : threeLineCharge * (zetaFiniteMultiplicityMass W +
      (13 / (2 * threeLineCharge) : Real) * zetaFiniteHorizontalMoment W) =
      threeLineCharge * zetaFiniteMultiplicityMass W +
        (13 / 2 : Real) * zetaFiniteHorizontalMoment W := by
    field_simp [threeLineCharge_pos.ne'] <;> ring
  rw [<- he] at h
  exact (_root_.mul_le_mul_iff_of_pos_left threeLineCharge_pos).mp h

theorem zeta_multiplicity_horizontal_profile {w : Complex}
    (hw : And (0 < w.re) (w.re < 1)) (ht : 2 <= abs w.im) :
    (analyticOrderNatAt riemannZeta w : Real) *
      (1 + (13 / (2 * threeLineCharge) : Real) * (w.re - 1 / 2) ^ 2) <=
        threeLineMultiplicityBudget w.im := by
  have h := zeta_finite_horizontal_budget_normalized w.im ht ({w} : Finset Complex)
    (fun z hz => by
      have he : z = w := Finset.mem_singleton.mp hz
      subst z
      exact hw)
    (fun z hz => by
      have he : z = w := Finset.mem_singleton.mp hz
      subst z
      rfl)
  simp only [zetaFiniteMultiplicityMass, zetaFiniteHorizontalMoment, Finset.sum_singleton] at h
  nlinarith only [h]

theorem zeta_finite_horizontal_rigidity (t : Real) (ht : 2 <= abs t) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t) (eta : Real)
    (hNear : (1 - eta) * threeLineMultiplicityBudget t <= zetaFiniteMultiplicityMass W) :
    (13 / (2 * threeLineCharge) : Real) * zetaFiniteHorizontalMoment W <=
      eta * threeLineMultiplicityBudget t := by
  have h := zeta_finite_horizontal_budget_normalized t ht W hCritical hSame
  nlinarith only [h, hNear]

end PrimeFactorOscillations
