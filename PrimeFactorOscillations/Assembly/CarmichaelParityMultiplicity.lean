/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNonlinearHorizontalMultiplicity
import PrimeFactorOscillations.Helpers.XiParityMultiplicity

/-! # A strict parity correction to the full nonlinear horizontal multiplicity budget

Reflection closure is required. The exact optimizer describes finite kernel
configurations, not equality in the analytic zeta trace ceiling. Total order1
is treated without division by N-1. No global simplicity or QRH gain is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

theorem zetaFiniteTotalOrder_eq_mass (W : Finset Complex) :
    (zetaFiniteTotalOrder W : Real) = zetaFiniteMultiplicityMass W :=
  zetaFiniteTotalOrder_cast W

theorem zeta_total_order_one_horizontal_geometry (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOne : zetaFiniteTotalOrder W = 1) :
    And (zetaFiniteHorizontalMoment W = 0) (zetaFiniteHorizontalFourthMoment W = 0) := by
  have hM := zeta_total_order_one_horizontal_moment_zero W hCritical hReflect hOne
  change zetaFiniteHorizontalMoment W = 0 at hM
  apply And.intro hM
  unfold zetaFiniteHorizontalFourthMoment
  apply Finset.sum_eq_zero
  intro w hw
  have hTerm : (analyticOrderNatAt riemannZeta w : Real) * (w.re - 1 / 2) ^ 2 = 0 := by
    have hLe := Finset.single_le_sum
      (fun v (_hv : Membership.mem W v) =>
        mul_nonneg (Nat.cast_nonneg (analyticOrderNatAt riemannZeta v)) (sq_nonneg (v.re - 1 / 2))) hw
    change (analyticOrderNatAt riemannZeta w : Real) * (w.re - 1 / 2) ^ 2 <=
      zetaFiniteHorizontalMoment W at hLe
    rw [hM] at hLe
    exact le_antisymm hLe (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  calc
    _ = ((analyticOrderNatAt riemannZeta w : Real) * (w.re - 1 / 2) ^ 2) *
        (w.re - 1 / 2) ^ 2 := by ring
    _ = 0 := by rw [hTerm, zero_mul]

theorem zeta_finite_odd_horizontal_budget (t : Real) (ht : 2 <= abs t)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t)
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W)) (hN : 1 < zetaFiniteMultiplicityMass W) :
    And (zetaFiniteHorizontalMoment W <= (9 / 64) * (zetaFiniteMultiplicityMass W - 1))
      (threeLineHorizontalVarianceCoefficient * zetaFiniteHorizontalFourthMoment W +
        threeLineCharge + (zetaFiniteMultiplicityMass W - 1) *
          threeLineHorizontalResidualProfile
            (zetaFiniteHorizontalMoment W / (zetaFiniteMultiplicityMass W - 1)) <=
              threeLineCharge * threeLineMultiplicityBudget t) := by
  have hDen : 0 < zetaFiniteMultiplicityMass W - 1 := by linarith
  have hCenter : zetaFiniteHorizontalMoment W = (zetaFiniteMultiplicityMass W - 1) *
      (zetaFiniteHorizontalMoment W / (zetaFiniteMultiplicityMass W - 1)) := by
    field_simp [hDen.ne']
  have h := zeta_finite_odd_horizontal_charge_trace t W hCritical hSame hReflect hOdd
    xi_seven_eighths_centered_strip
      (zetaFiniteHorizontalMoment W / (zetaFiniteMultiplicityMass W - 1))
        (by rw [zetaFiniteTotalOrder_eq_mass]; exact hN)
        (by rw [zetaFiniteTotalOrder_eq_mass]; exact hCenter)
  rw [zetaFiniteTotalOrder_eq_mass] at h
  have hMax := _root_.mul_le_mul_of_nonneg_left h.1.2 (le_of_lt hDen)
  have hMMax : zetaFiniteHorizontalMoment W <= (9 / 64) * (zetaFiniteMultiplicityMass W - 1) := by
    rw [<- hCenter] at hMax
    nlinarith
  have hUpper := xi_threeLine_trace_upper t ht
  have hUpperEq : (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) / 2 *
      Real.log (abs t) + (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) *
        threeLineHeightConstant + threeLineLipschitzConstant * threeLineRemainderScale =
      threeLineCharge * threeLineMultiplicityBudget t := by
    unfold threeLineMultiplicityBudget threeLineLeadingCoefficient threeLineMultiplicityConstant
    field_simp [threeLineCharge_pos.ne']
    ring
  rw [hUpperEq] at hUpper
  exact And.intro hMMax (h.2.trans hUpper)

theorem zeta_horizontal_full_charge_residual_identity (W : Finset Complex)
    (hN : 0 < zetaFiniteMultiplicityMass W) :
    zetaFiniteMultiplicityMass W * threeLineHorizontalProfile (zetaFiniteHorizontalMean W) +
      threeLineHorizontalVarianceCoefficient *
        zetaFiniteHorizontalVariance W (zetaFiniteHorizontalMean W) =
      threeLineHorizontalVarianceCoefficient * zetaFiniteHorizontalFourthMoment W +
        zetaFiniteMultiplicityMass W *
          threeLineHorizontalResidualProfile (zetaFiniteHorizontalMean W) := by
  rw [zetaFiniteHorizontalVariance_identity]
  unfold threeLineHorizontalResidualProfile
  rw [zetaFiniteHorizontalMean_balance W hN]
  ring

theorem zeta_finite_odd_horizontal_parity_budget (t : Real) (ht : 2 <= abs t)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t)
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W)) (hN : 1 < zetaFiniteMultiplicityMass W) :
    zetaFiniteMultiplicityMass W * threeLineHorizontalProfile (zetaFiniteHorizontalMean W) +
      threeLineHorizontalVarianceCoefficient *
        zetaFiniteHorizontalVariance W (zetaFiniteHorizontalMean W) +
      threeLineParityCost (zetaFiniteMultiplicityMass W) (zetaFiniteHorizontalMoment W) <=
        threeLineCharge * threeLineMultiplicityBudget t := by
  have h := (zeta_finite_odd_horizontal_budget t ht W hCritical hSame hReflect hOdd hN).2
  rw [zeta_horizontal_full_charge_residual_identity W (by linarith)]
  unfold threeLineParityCost
  change _ + (threeLineCharge + (zetaFiniteMultiplicityMass W - 1) *
    threeLineHorizontalResidualProfile
      (zetaFiniteHorizontalMoment W / (zetaFiniteMultiplicityMass W - 1)) -
    zetaFiniteMultiplicityMass W * threeLineHorizontalResidualProfile (zetaFiniteHorizontalMean W)) <= _
  linarith

theorem zeta_odd_horizontal_parity_cost (t : Real) (ht : 2 <= abs t)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t)
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W)) (hN : 1 < zetaFiniteMultiplicityMass W) :
    And (0 <= threeLineParityCost (zetaFiniteMultiplicityMass W) (zetaFiniteHorizontalMoment W))
      (0 < zetaFiniteHorizontalMoment W ->
        0 < threeLineParityCost (zetaFiniteMultiplicityMass W) (zetaFiniteHorizontalMoment W)) := by
  have hMax := (zeta_finite_odd_horizontal_budget t ht W hCritical hSame hReflect hOdd hN).1
  exact And.intro
    (threeLineParityCost_nonneg _ _ hN (zetaFiniteHorizontalMoment_nonneg W) hMax)
    (fun hM => threeLineParityCost_pos _ _ hN hM hMax)

end PrimeFactorOscillations
