/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.ThreeLineResolventCertificate
import PrimeFactorOscillations.Helpers.XiEffectiveBounds
import PrimeFactorOscillations.Helpers.XiPairedResolventTrace
import PrimeFactorOscillations.Helpers.XiZetaMultiplicity

/-! # The full signed three-line multiplicity consumer -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

def threeLineXiTrace (t : Real) : Real :=
  threeLineWeight1 * xiPairedLogTrace threeLineRadius1 t +
    threeLineWeight2 * xiPairedLogTrace threeLineRadius2 t +
    threeLineWeight3 * xiPairedLogTrace threeLineRadius3 t

def threeLineHeightConstant : Real :=
  xiExplicitHeight (1 / 2 + threeLineRadius1) (1 / 2 + threeLineRadius1)

def threeLineLipschitzConstant : Real := xiExplicitLipschitz (1 / 2 + threeLineRadius1)

def threeLineRemainderScale : Real :=
  abs threeLineWeight2 * abs (threeLineRadius2 - threeLineRadius1) +
    abs threeLineWeight3 * abs (threeLineRadius3 - threeLineRadius1)

def threeLineMultiplicityConstant : Real :=
  ((threeLineWeight1 + threeLineWeight2 + threeLineWeight3) * threeLineHeightConstant +
    threeLineLipschitzConstant * threeLineRemainderScale) / threeLineCharge

theorem xi_threeLine_kernel_summable (t : Real) :
    Summable (fun p : RiemannXiDivisorZeroIndex => threeLineKernel
      ((riemannXiDivisorZeroValue p).re - 1 / 2) (t - (riemannXiDivisorZeroValue p).im)) := by
  have h1 := (xi_paired_resolvent_summable threeLineRadius1 t
    (by norm_num [threeLineRadius1])).mul_left threeLineWeight1
  have h2 := (xi_paired_resolvent_summable threeLineRadius2 t
    (by norm_num [threeLineRadius2])).mul_left threeLineWeight2
  have h3 := (xi_paired_resolvent_summable threeLineRadius3 t
    (by norm_num [threeLineRadius3])).mul_left threeLineWeight3
  exact (h1.add h2).add h3

theorem xi_threeLine_kernel_trace (t : Real) :
    threeLineXiTrace t = tsum (fun p : RiemannXiDivisorZeroIndex => threeLineKernel
      ((riemannXiDivisorZeroValue p).re - 1 / 2) (t - (riemannXiDivisorZeroValue p).im)) := by
  have h1 := (xi_paired_resolvent_summable threeLineRadius1 t
    (by norm_num [threeLineRadius1])).mul_left threeLineWeight1
  have h2 := (xi_paired_resolvent_summable threeLineRadius2 t
    (by norm_num [threeLineRadius2])).mul_left threeLineWeight2
  have h3 := (xi_paired_resolvent_summable threeLineRadius3 t
    (by norm_num [threeLineRadius3])).mul_left threeLineWeight3
  unfold threeLineXiTrace threeLineKernel
  rw [xi_paired_resolvent_trace _ _ (by norm_num [threeLineRadius1]),
    xi_paired_resolvent_trace _ _ (by norm_num [threeLineRadius2]),
    xi_paired_resolvent_trace _ _ (by norm_num [threeLineRadius3])]
  rw [(h1.add h2).tsum_add h3, h1.tsum_add h2]
  simp only [tsum_mul_left]

theorem xi_threeLine_finite_mass (t : Real)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8)
    (S : Finset RiemannXiDivisorZeroIndex) :
    Finset.sum S (fun p => threeLineKernel ((riemannXiDivisorZeroValue p).re - 1 / 2)
      (t - (riemannXiDivisorZeroValue p).im)) <= threeLineXiTrace t := by
  rw [xi_threeLine_kernel_trace]
  exact (xi_threeLine_kernel_summable t).sum_le_tsum S
    (fun p _ => (threeLineKernel_pos _ _ (hStrip p)).le)

theorem zeta_multiplicity_le_threeLine_trace {w : Complex}
    (hw : And (0 < w.re) (w.re < 1))
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8) :
    (analyticOrderNatAt riemannZeta w : Real) * threeLineCharge <= threeLineXiTrace w.im := by
  classical
  have hw0 : Not (w = 0) := by intro h; simp [h] at hw
  have hw1 : Not (w = 1) := by intro h; simp [h] at hw
  have hu : abs (w.re - 1 / 2) <= 1 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith only [hw.1, hw.2]
  let f : RiemannXiDivisorZeroIndex -> Real := fun p =>
    threeLineKernel ((riemannXiDivisorZeroValue p).re - 1 / 2)
      (w.im - (riemannXiDivisorZeroValue p).im)
  let e := xiZeroFiberEquiv w hw0
  let j : Fin (xiZeroMultiplicity w) -> RiemannXiDivisorZeroIndex :=
    fun k => (e.symm k).val
  have hj : Function.Injective j := by
    intro a b h
    apply e.symm.injective
    exact Subtype.ext h
  have hv (k : Fin (xiZeroMultiplicity w)) : riemannXiDivisorZeroValue (j k) = w :=
    (e.symm k).property
  let S : Finset RiemannXiDivisorZeroIndex := Finset.univ.image j
  have hFinite : (xiZeroMultiplicity w : Real) * threeLineCharge <= Finset.sum S f := by
    dsimp only [S]
    rw [Finset.sum_image (fun a _ b _ h => hj h)]
    calc
      (xiZeroMultiplicity w : Real) * threeLineCharge =
          Finset.sum Finset.univ (fun _ : Fin (xiZeroMultiplicity w) => threeLineCharge) := by simp
      _ <= _ := by
        apply Finset.sum_le_sum
        intro k _
        change threeLineCharge <= threeLineKernel ((riemannXiDivisorZeroValue (j k)).re - 1 / 2)
          (w.im - (riemannXiDivisorZeroValue (j k)).im)
        rw [hv, sub_self]
        exact threeLineKernel_same_height_ge _ hu
  have hTotal := xi_threeLine_finite_mass w.im hStrip S
  rw [<- xiZeroMultiplicity_eq_zetaOrder hw.1 hw1]
  exact hFinite.trans hTotal

theorem xi_threeLine_base_height (t : Real) (ht : 2 <= abs t) :
    xiPairedLogTrace threeLineRadius1 t <= (1 / 2 : Real) * Real.log (abs t) +
      threeLineHeightConstant := by
  let a : Real := 1 / 2 + threeLineRadius1
  have ha : 1 < a := by norm_num [a, threeLineRadius1]
  have hRe (r t : Real) : (xiResolventPoint r t).re = 1 / 2 + r := by simp [xiResolventPoint]
  have hIm (r t : Real) : (xiResolventPoint r t).im = t := by simp [xiResolventPoint]
  have hp := xi_logDeriv_explicit_height a a ha (xiResolventPoint threeLineRadius1 t)
    (by simp [hRe, a]) (by simp [hRe, a]) (by simpa only [hIm] using ht)
  have hm := xi_logDeriv_explicit_height a a ha (xiResolventPoint threeLineRadius1 (-t))
    (by simp [hRe, a]) (by simp [hRe, a]) (by simpa only [hIm, abs_neg] using ht)
  simp only [hIm, abs_neg] at hp hm
  unfold xiPairedLogTrace threeLineHeightConstant
  linarith only [hp, hm]

theorem xi_threeLine_radius_deviation (r t : Real) (hr : threeLineRadius1 <= r) :
    abs (xiPairedLogTrace r t - xiPairedLogTrace threeLineRadius1 t) <=
      threeLineLipschitzConstant * abs (r - threeLineRadius1) := by
  let a : Real := 1 / 2 + threeLineRadius1
  have ha : 1 < a := by norm_num [a, threeLineRadius1]
  have hRe (r t : Real) : (xiResolventPoint r t).re = 1 / 2 + r := by simp [xiResolventPoint]
  have hbase (t : Real) : a <= (xiResolventPoint threeLineRadius1 t).re := by simp [hRe, a]
  have hrad (t : Real) : a <= (xiResolventPoint r t).re := by
    rw [hRe]
    dsimp only [a]
    linarith only [hr]
  have hnorm (t : Real) : norm (xiResolventPoint r t - xiResolventPoint threeLineRadius1 t) =
      abs (r - threeLineRadius1) := by
    have he : xiResolventPoint r t - xiResolventPoint threeLineRadius1 t =
        ((r - threeLineRadius1 : Real) : Complex) := by
      simp only [xiResolventPoint, Complex.ofReal_sub]
      ring
    rw [he]
    simp only [Complex.norm_real, Real.norm_eq_abs]
  have hp := xi_logDeriv_explicit_lipschitz a ha
    (xiResolventPoint threeLineRadius1 t) (xiResolventPoint r t) (hbase t) (hrad t)
  have hm := xi_logDeriv_explicit_lipschitz a ha
    (xiResolventPoint threeLineRadius1 (-t)) (xiResolventPoint r (-t)) (hbase (-t)) (hrad (-t))
  rw [hnorm] at hp hm
  have hdp := (Complex.abs_re_le_norm _).trans hp
  have hdm := (Complex.abs_re_le_norm _).trans hm
  simp only [Complex.sub_re] at hdp hdm
  have hpp := abs_le.mp hdp
  have hmp := abs_le.mp hdm
  apply abs_le.mpr
  constructor <;> unfold xiPairedLogTrace threeLineLipschitzConstant <;>
    linarith only [hpp.1, hpp.2, hmp.1, hmp.2]

theorem xi_threeLine_trace_upper (t : Real) (ht : 2 <= abs t) :
    threeLineXiTrace t <=
      (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) / 2 * Real.log (abs t) +
      (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) * threeLineHeightConstant +
      threeLineLipschitzConstant * threeLineRemainderScale := by
  have hbase := xi_threeLine_base_height t ht
  have h2 := xi_threeLine_radius_deviation threeLineRadius2 t
    (by norm_num [threeLineRadius1, threeLineRadius2])
  have h3 := xi_threeLine_radius_deviation threeLineRadius3 t
    (by norm_num [threeLineRadius1, threeLineRadius3])
  have hs : 0 <= threeLineWeight1 + threeLineWeight2 + threeLineWeight3 := by
    norm_num [threeLineWeight1, threeLineWeight2, threeLineWeight3]
  have hmain := mul_le_mul_of_nonneg_left hbase hs
  have he2 : threeLineWeight2 * (xiPairedLogTrace threeLineRadius2 t -
      xiPairedLogTrace threeLineRadius1 t) <= abs threeLineWeight2 *
        (threeLineLipschitzConstant * abs (threeLineRadius2 - threeLineRadius1)) := by
    calc
      _ <= abs (threeLineWeight2 * (xiPairedLogTrace threeLineRadius2 t -
        xiPairedLogTrace threeLineRadius1 t)) := le_abs_self _
      _ = _ := abs_mul _ _
      _ <= _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have he3 : threeLineWeight3 * (xiPairedLogTrace threeLineRadius3 t -
      xiPairedLogTrace threeLineRadius1 t) <= abs threeLineWeight3 *
        (threeLineLipschitzConstant * abs (threeLineRadius3 - threeLineRadius1)) := by
    calc
      _ <= abs (threeLineWeight3 * (xiPairedLogTrace threeLineRadius3 t -
        xiPairedLogTrace threeLineRadius1 t)) := le_abs_self _
      _ = _ := abs_mul _ _
      _ <= _ := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  have hid : threeLineXiTrace t =
      (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) * xiPairedLogTrace threeLineRadius1 t +
      threeLineWeight2 * (xiPairedLogTrace threeLineRadius2 t - xiPairedLogTrace threeLineRadius1 t) +
      threeLineWeight3 * (xiPairedLogTrace threeLineRadius3 t - xiPairedLogTrace threeLineRadius1 t) := by
    unfold threeLineXiTrace
    ring
  rw [hid]
  calc
    _ <= (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) *
        ((1 / 2 : Real) * Real.log (abs t) + threeLineHeightConstant) +
      abs threeLineWeight2 * (threeLineLipschitzConstant * abs (threeLineRadius2 - threeLineRadius1)) +
      abs threeLineWeight3 * (threeLineLipschitzConstant * abs (threeLineRadius3 - threeLineRadius1)) :=
        add_le_add (add_le_add hmain he2) he3
    _ = _ := by unfold threeLineRemainderScale; ring

theorem zeta_multiplicity_le_threeLine_bound {w : Complex}
    (hw : And (0 < w.re) (w.re < 1)) (ht : 2 <= abs w.im)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8) :
    (analyticOrderNatAt riemannZeta w : Real) <=
      threeLineLeadingCoefficient * Real.log (abs w.im) + threeLineMultiplicityConstant := by
  have hh := (zeta_multiplicity_le_threeLine_trace hw hStrip).trans (xi_threeLine_trace_upper w.im ht)
  have he : (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) / 2 * Real.log (abs w.im) +
      (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) * threeLineHeightConstant +
      threeLineLipschitzConstant * threeLineRemainderScale =
        (threeLineLeadingCoefficient * Real.log (abs w.im) + threeLineMultiplicityConstant) *
          threeLineCharge := by
    unfold threeLineLeadingCoefficient threeLineMultiplicityConstant
    field_simp [threeLineCharge_pos.ne'] <;> ring
  rw [he] at hh
  exact (mul_le_mul_iff_of_pos_right threeLineCharge_pos).mp hh

end PrimeFactorOscillations
