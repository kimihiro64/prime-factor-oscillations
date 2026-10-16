/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.XiZeroMultiplicity

/-!
# Xi and zeta multiplicities

The completed factors are analytic nonzero units in the positive half-plane away from one. The critical-line order is the actual zeta order.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations

def xiZetaUnit (s : Complex) : Complex :=
  s * (s - 1) / 2 * Complex.exp (Complex.log (Real.pi : Complex) * (-s / 2)) *
    Complex.Gamma (s / 2)

theorem gamma_analyticAt_of_re_pos {z : Complex} (hz : 0 < z.re) :
    AnalyticAt Complex Complex.Gamma z := by
  have hDiff : DifferentiableOn Complex Complex.Gamma {s : Complex | 0 < s.re} := by
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    apply Complex.differentiableAt_Gamma s
    intro m hm
    have h := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at h
    have hn : (0 : Real) <= m := Nat.cast_nonneg m
    change 0 < s.re at hs
    linarith
  have hOpen : IsOpen {s : Complex | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  exact hDiff.analyticOnNhd hOpen z hz

theorem xiZetaUnit_analyticAt {z : Complex} (hz : 0 < z.re) :
    AnalyticAt Complex xiZetaUnit z := by
  have hHalf : 0 < (z / 2).re := by simpa only [Complex.div_ofNat_re] using half_pos hz
  have hId : AnalyticAt Complex (fun s : Complex => s) z := analyticAt_id
  have hDiv : AnalyticAt Complex (fun s : Complex => s / 2) z := hId.div_const
  have hGamma : AnalyticAt Complex (fun s : Complex => Complex.Gamma (s / 2)) z :=
    (gamma_analyticAt_of_re_pos hHalf).comp
      (g := Complex.Gamma) (f := fun s : Complex => s / 2) hDiv
  have hExp : AnalyticAt Complex
      (fun s : Complex => Complex.exp (Complex.log (Real.pi : Complex) * (-s / 2))) z :=
    (analyticAt_const.mul hId.neg.div_const).cexp
  exact (((hId.mul (hId.sub analyticAt_const)).div_const).mul hExp).mul hGamma

theorem xiZetaUnit_ne_zero {z : Complex} (hz : 0 < z.re) (h1 : Not (z = 1)) :
    Not (xiZetaUnit z = 0) := by
  have h0 : Not (z = 0) := by intro h; simpa [h] using hz
  have hHalf : 0 < (z / 2).re := by simpa only [Complex.div_ofNat_re] using half_pos hz
  exact mul_ne_zero
    (mul_ne_zero (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) (by norm_num))
      (Complex.exp_ne_zero _))
    (Complex.Gamma_ne_zero_of_re_pos hHalf)

theorem riemannXi_eq_xiZetaUnit_mul {z : Complex} (hz : 0 < z.re) (h1 : Not (z = 1)) :
    Complex.riemannXi z = xiZetaUnit z * riemannZeta z := by
  have h0 : Not (z = 0) := by intro h; simpa [h] using hz
  have hHalf : 0 < (z / 2).re := by simpa only [Complex.div_ofNat_re] using half_pos hz
  have hPi : Not ((Real.pi : Complex) = 0) := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.riemannXi_eq_mul_completedRiemannZeta h0 h1,
    completedRiemannZeta_eq_cpow_mul_Gamma_mul_riemannZeta h0
      (Complex.Gamma_ne_zero_of_re_pos hHalf),
    Complex.cpow_def_of_ne_zero hPi]
  unfold xiZetaUnit
  ring

theorem analyticOrderAt_xi_eq_zeta {z : Complex} (hz : 0 < z.re) (h1 : Not (z = 1)) :
    analyticOrderAt Complex.riemannXi z = analyticOrderAt riemannZeta z := by
  have hPos : Filter.Eventually (fun s : Complex => 0 < s.re) (nhds z) :=
    (Complex.continuous_re.tendsto z).eventually (eventually_gt_nhds hz)
  have hOne : Filter.Eventually (fun s : Complex => Not (s = 1)) (nhds z) :=
    eventually_ne_nhds h1
  have hEq : Filter.EventuallyEq (nhds z) Complex.riemannXi (xiZetaUnit * riemannZeta) := by
    filter_upwards [hPos, hOne] with s hs hs1
    exact riemannXi_eq_xiZetaUnit_mul hs hs1
  have hUnit := xiZetaUnit_analyticAt hz
  have hZeta : AnalyticAt Complex riemannZeta z := analyticOn_riemannZeta z h1
  rw [analyticOrderAt_congr hEq, analyticOrderAt_mul hUnit hZeta,
    hUnit.analyticOrderAt_eq_zero.mpr (xiZetaUnit_ne_zero hz h1), zero_add]

theorem xiZeroMultiplicity_eq_zetaOrder {z : Complex} (hz : 0 < z.re) (h1 : Not (z = 1)) :
    xiZeroMultiplicity z = analyticOrderNatAt riemannZeta z := by
  unfold xiZeroMultiplicity
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int Complex.differentiable_riemannXi]
  simp only [Int.toNat_natCast]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_xi_eq_zeta hz h1]

theorem xiZeroMultiplicity_criticalLine_eq_zetaOrder (w : Real) :
    xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I) =
      analyticOrderNatAt riemannZeta ((1 / 2 : Complex) + (w : Complex) * Complex.I) := by
  apply xiZeroMultiplicity_eq_zetaOrder
  . norm_num
  . intro h
    have hr := congrArg Complex.re h
    norm_num at hr

theorem xiZeroMultiplicity_eq_analyticOrderNatAt (z : Complex) :
    xiZeroMultiplicity z = analyticOrderNatAt Complex.riemannXi z := by
  unfold xiZeroMultiplicity
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int Complex.differentiable_riemannXi]
  simp

theorem analyticOrderAt_xi_ne_top (z : Complex) :
    Not (analyticOrderAt Complex.riemannXi z = Top.top) := by
  intro hTop
  have hLocal := analyticOrderAt_eq_top.mp hTop
  have hAnalytic : AnalyticOnNhd Complex Complex.riemannXi Set.univ :=
    fun s _ => Complex.differentiable_riemannXi.analyticAt s
  have hGlobal := hAnalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) hLocal
  have hZero := hGlobal (Set.mem_univ (0 : Complex))
  norm_num [Complex.riemannXi_zero] at hZero

theorem xiZeroMultiplicity_pos_iff (z : Complex) :
    0 < xiZeroMultiplicity z <-> Complex.riemannXi z = 0 := by
  rw [xiZeroMultiplicity_eq_analyticOrderNatAt, Nat.pos_iff_ne_zero]
  constructor
  . exact apply_eq_zero_of_analyticOrderNatAt_ne_zero
  . intro hZero hNat
    have hA := Complex.differentiable_riemannXi.analyticAt z
    have hNonzero := hA.analyticOrderAt_ne_zero.mpr hZero
    cases hOrder : analyticOrderAt Complex.riemannXi z with
    | top => exact (analyticOrderAt_xi_ne_top z hOrder).elim
    | coe n =>
      have hn : n = 0 := by simpa [analyticOrderNatAt, hOrder] using hNat
      apply hNonzero
      rw [hOrder, hn]
      rfl

theorem xiZeroMultiplicity_criticalLine_pos_iff_zeta_zero (w : Real) :
    0 < xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I) <->
      riemannZeta ((1 / 2 : Complex) + (w : Complex) * Complex.I) = 0 := by
  let z : Complex := (1 / 2 : Complex) + (w : Complex) * Complex.I
  have hz : 0 < z.re := by norm_num [z]
  have h1 : Not (z = 1) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [z] at hr
  rw [xiZeroMultiplicity_pos_iff, riemannXi_eq_xiZetaUnit_mul hz h1]
  simp only [mul_eq_zero, xiZetaUnit_ne_zero hz h1, false_or]
  rfl

end PrimeFactorOscillations
