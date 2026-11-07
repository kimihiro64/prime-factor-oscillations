/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelParityMultiplicity
import PrimeFactorOscillations.Helpers.ThreeLineParityCubic

/-! # Sharp cubic charging of actual odd zeta clusters

All old nonlinear and quartic charges remain in the trace slack. This gives
an explicit inverse geometric constraint, not a global simplicity theorem.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

def threeLineHorizontalTraceSlack (t : Real) (W : Finset Complex) : Real :=
  threeLineCharge * threeLineMultiplicityBudget t -
    (zetaFiniteMultiplicityMass W * threeLineHorizontalProfile (zetaFiniteHorizontalMean W) +
      threeLineHorizontalVarianceCoefficient *
        zetaFiniteHorizontalVariance W (zetaFiniteHorizontalMean W))

theorem zeta_finite_odd_horizontal_cubic_budget (t : Real) (ht : 2 <= abs t)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t)
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W)) (hN : 1 < zetaFiniteMultiplicityMass W) :
    zetaFiniteMultiplicityMass W * threeLineHorizontalProfile (zetaFiniteHorizontalMean W) +
      threeLineHorizontalVarianceCoefficient *
        zetaFiniteHorizontalVariance W (zetaFiniteHorizontalMean W) +
      threeLineParityCubicCoefficient * threeLineParityCubicScale (zetaFiniteMultiplicityMass W) *
        (zetaFiniteHorizontalMoment W) ^ 3 <= threeLineCharge * threeLineMultiplicityBudget t := by
  have hMax := (zeta_finite_odd_horizontal_budget t ht W hCritical hSame hReflect hOdd hN).1
  have hCubic := threeLineParityCost_cubic_lower (zetaFiniteMultiplicityMass W)
    (zetaFiniteHorizontalMoment W) hN (zetaFiniteHorizontalMoment_nonneg W) hMax
  have hFull := zeta_finite_odd_horizontal_parity_budget t ht W hCritical hSame hReflect hOdd hN
  linarith

theorem zeta_odd_horizontal_cubic_inverse (t : Real) (ht : 2 <= abs t)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t)
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W)) (hN : 1 < zetaFiniteMultiplicityMass W) :
    threeLineParityCubicCoefficient * (2 * zetaFiniteMultiplicityMass W - 1) *
      (zetaFiniteHorizontalMoment W) ^ 3 <=
      (zetaFiniteMultiplicityMass W) ^ 2 * (zetaFiniteMultiplicityMass W - 1) ^ 2 *
        threeLineHorizontalTraceSlack t W := by
  have hFull := zeta_finite_odd_horizontal_cubic_budget t ht W hCritical hSame hReflect hOdd hN
  have hSlack : threeLineParityCubicCoefficient * threeLineParityCubicScale (zetaFiniteMultiplicityMass W) *
      (zetaFiniteHorizontalMoment W) ^ 3 <= threeLineHorizontalTraceSlack t W := by
    unfold threeLineHorizontalTraceSlack
    linarith
  have hNp : 0 < zetaFiniteMultiplicityMass W := by linarith
  have hQp : 0 < zetaFiniteMultiplicityMass W - 1 := by linarith
  have hDen : 0 < (zetaFiniteMultiplicityMass W) ^ 2 * (zetaFiniteMultiplicityMass W - 1) ^ 2 :=
    mul_pos (pow_pos hNp 2) (pow_pos hQp 2)
  have hProduct := _root_.mul_le_mul_of_nonneg_right hSlack (le_of_lt hDen)
  have hEq : (threeLineParityCubicCoefficient * threeLineParityCubicScale (zetaFiniteMultiplicityMass W) *
      (zetaFiniteHorizontalMoment W) ^ 3) *
        ((zetaFiniteMultiplicityMass W) ^ 2 * (zetaFiniteMultiplicityMass W - 1) ^ 2) =
      threeLineParityCubicCoefficient * (2 * zetaFiniteMultiplicityMass W - 1) *
        (zetaFiniteHorizontalMoment W) ^ 3 := by
    unfold threeLineParityCubicScale
    field_simp [hNp.ne', hQp.ne'] <;> ring
  rw [hEq] at hProduct
  simpa only [mul_comm (threeLineHorizontalTraceSlack t W)] using hProduct

theorem zeta_odd_horizontal_cubic_slack_strict (t : Real) (ht : 2 <= abs t)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t)
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W)) (hN : 1 < zetaFiniteMultiplicityMass W)
    (hM : 0 < zetaFiniteHorizontalMoment W) :
    threeLineParityCubicCoefficient * threeLineParityCubicScale (zetaFiniteMultiplicityMass W) *
      (zetaFiniteHorizontalMoment W) ^ 3 < threeLineHorizontalTraceSlack t W := by
  have hMax := (zeta_finite_odd_horizontal_budget t ht W hCritical hSame hReflect hOdd hN).1
  have hCubic := threeLineParityCost_cubic_strict (zetaFiniteMultiplicityMass W)
    (zetaFiniteHorizontalMoment W) hN hM hMax
  have hFull := zeta_finite_odd_horizontal_parity_budget t ht W hCritical hSame hReflect hOdd hN
  unfold threeLineHorizontalTraceSlack
  linarith

end PrimeFactorOscillations
