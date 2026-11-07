/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelClusterMultiplicity
import PrimeFactorOscillations.Helpers.XiExactWindowMultiplicity

/-! # Unconditional exact width-dependent multiplicity bounds -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

def threeLineExactWindowCoefficient (h : Real) : Real :=
  (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) /
    (2 * threeLineExactWindowCharge h)

def threeLineExactWindowConstant (h : Real) : Real :=
  threeLineCharge / threeLineExactWindowCharge h * threeLineMultiplicityConstant

theorem threeLineExactWindowCoefficient_pos (h : Real) :
    0 < threeLineExactWindowCoefficient h := by
  unfold threeLineExactWindowCoefficient
  exact div_pos (by norm_num [threeLineWeight1, threeLineWeight2, threeLineWeight3])
    (mul_pos (by norm_num) (threeLineExactWindowCharge_pos h))

theorem threeLineExactWindowConstant_nonneg (h : Real) :
    0 <= threeLineExactWindowConstant h := by
  unfold threeLineExactWindowConstant
  exact mul_nonneg (div_nonneg threeLineCharge_pos.le (threeLineExactWindowCharge_pos h).le)
    threeLineMultiplicityConstant_nonneg

theorem zeta_finite_exact_window_bound (T : Real) (hT : 2 <= abs T)
    (h : Real) (h0 : 0 <= h) (hMax : h <= 3 / 20) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hWindow : forall w, Membership.mem W w -> abs (T - w.im) <= h) :
    zetaFiniteMultiplicityMass W <= threeLineExactWindowCoefficient h * Real.log (abs T) +
      threeLineExactWindowConstant h := by
  have hh := (zeta_finite_exact_window_charge_trace T h h0 hMax W hCritical hWindow
    xi_seven_eighths_centered_strip).trans (xi_threeLine_trace_upper T hT)
  have hMass : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      threeLineExactWindowCharge h) = threeLineExactWindowCharge h * zetaFiniteMultiplicityMass W := by
    unfold zetaFiniteMultiplicityMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  have hUpper : (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) / 2 *
      Real.log (abs T) + (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) *
        threeLineHeightConstant + threeLineLipschitzConstant * threeLineRemainderScale =
      threeLineExactWindowCharge h * (threeLineExactWindowCoefficient h * Real.log (abs T) +
        threeLineExactWindowConstant h) := by
    unfold threeLineExactWindowCoefficient threeLineExactWindowConstant threeLineMultiplicityConstant
    field_simp [(threeLineExactWindowCharge_pos h).ne', threeLineCharge_pos.ne'] <;> ring
  rw [hMass, hUpper] at hh
  exact (_root_.mul_le_mul_iff_of_pos_left (threeLineExactWindowCharge_pos h)).mp hh

theorem zeta_finite_exact_sixteenth_window (T : Real) (hT : 2 <= abs T) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hWindow : forall w, Membership.mem W w -> abs (T - w.im) <= 1 / 16) :
    zetaFiniteMultiplicityMass W <= (24507727000183581493 / 180840288877455431220 : Real) * Real.log (abs T) +
      threeLineExactWindowConstant (1 / 16) := by
  have hh := zeta_finite_exact_window_bound T hT (1 / 16) (by norm_num) (by norm_num)
    W hCritical hWindow
  have hc : threeLineExactWindowCoefficient (1 / 16) = (24507727000183581493 / 180840288877455431220 : Real) := by
    unfold threeLineExactWindowCoefficient
    rw [threeLineExactWindowCharge_eq_axis]
    norm_num [threeLineAxisRational, threeLineRadius1, threeLineRadius2, threeLineRadius3,
      threeLineWeight1, threeLineWeight2, threeLineWeight3]
  simpa only [hc] using hh

theorem zeta_finite_exact_eighth_window (T : Real) (hT : 2 <= abs T) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hWindow : forall w, Membership.mem W w -> abs (T - w.im) <= 1 / 8) :
    zetaFiniteMultiplicityMass W <= (3307467502813082321 / 22628332539800442840 : Real) * Real.log (abs T) +
      threeLineExactWindowConstant (1 / 8) := by
  have hh := zeta_finite_exact_window_bound T hT (1 / 8) (by norm_num) (by norm_num)
    W hCritical hWindow
  have hc : threeLineExactWindowCoefficient (1 / 8) = (3307467502813082321 / 22628332539800442840 : Real) := by
    unfold threeLineExactWindowCoefficient
    rw [threeLineExactWindowCharge_eq_axis]
    norm_num [threeLineAxisRational, threeLineRadius1, threeLineRadius2, threeLineRadius3,
      threeLineWeight1, threeLineWeight2, threeLineWeight3]
  simpa only [hc] using hh

theorem zeta_finite_exact_maximum_window (T : Real) (hT : 2 <= abs T) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hWindow : forall w, Membership.mem W w -> abs (T - w.im) <= 3 / 20) :
    zetaFiniteMultiplicityMass W <= (319946206530171 / 2096481612731132 : Real) * Real.log (abs T) +
      threeLineExactWindowConstant (3 / 20) := by
  have hh := zeta_finite_exact_window_bound T hT (3 / 20) (by norm_num) (by norm_num)
    W hCritical hWindow
  have hc : threeLineExactWindowCoefficient (3 / 20) = (319946206530171 / 2096481612731132 : Real) := by
    unfold threeLineExactWindowCoefficient
    rw [threeLineExactWindowCharge_eq_axis]
    norm_num [threeLineAxisRational, threeLineRadius1, threeLineRadius2, threeLineRadius3,
      threeLineWeight1, threeLineWeight2, threeLineWeight3]
  simpa only [hc] using hh

theorem threeLine_exact_maximum_dominates_old_sixteenth (T : Real) (hT : 2 <= abs T) :
    (319946206530171 / 2096481612731132 : Real) * Real.log (abs T) +
      threeLineExactWindowConstant (3 / 20) <=
    (4625194854 / 28457195785 : Real) * Real.log (abs T) + threeLineClusterWindowConstant := by
  have hLog : 0 <= Real.log (abs T) := Real.log_nonneg (by linarith only [hT])
  have hCoefficient : (319946206530171 / 2096481612731132 : Real) <=
      (4625194854 / 28457195785 : Real) := by norm_num
  have hLead := mul_le_mul_of_nonneg_right hCoefficient hLog
  have hRatio : threeLineCharge / threeLineExactWindowCharge (3 / 20) <=
      threeLineCharge / (threeLineCharge - 3 / 16) := by
    rw [threeLineExactWindowCharge_eq_axis]
    norm_num [threeLineAxisRational, threeLineCharge, threeLineRadius1, threeLineRadius2,
      threeLineRadius3, threeLineWeight1, threeLineWeight2, threeLineWeight3]
  have hConstant := mul_le_mul_of_nonneg_right hRatio threeLineMultiplicityConstant_nonneg
  change (319946206530171 / 2096481612731132 : Real) * Real.log (abs T) +
      threeLineCharge / threeLineExactWindowCharge (3 / 20) * threeLineMultiplicityConstant <=
    (4625194854 / 28457195785 : Real) * Real.log (abs T) +
      threeLineCharge / (threeLineCharge - 3 / 16) * threeLineMultiplicityConstant
  exact _root_.add_le_add hLead hConstant

end PrimeFactorOscillations
