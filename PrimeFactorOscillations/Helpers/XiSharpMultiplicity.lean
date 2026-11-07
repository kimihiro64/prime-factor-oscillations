/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import PrimeFactorOscillations.Helpers.XiPairedResolventTrace
import PrimeFactorOscillations.Helpers.XiVerticalLogDerivative
import PrimeFactorOscillations.Helpers.XiZetaMultiplicity
import PrimeFactorOscillations.Mathlib.Analysis.Complex.PairedResolventOptimizer

/-!
# Multiplicity bounds from an exact positive finite-strip kernel

The hypotheses give a genuine strip for the canonical xi zero enumeration.
All multiplicity copies and the signed compensation are retained before using
independent Euler and gamma bounds to estimate the observable.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Complex Robin1984

theorem xi_compensated_resolvent_finite_mass_of_positive_strip
    (width r R t : Real) (hwidth : 0 <= width) (hwidthr : width < r)
    (hr : 1 / 2 < r) (hR : r < R)
    (hPos : 2 * width <= Real.sqrt (r ^ 2 - width ^ 2) + Real.sqrt (R ^ 2 - width ^ 2))
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= width)
    (S : Finset RiemannXiDivisorZeroIndex) :
    Finset.sum S (fun p => pairedResolventDifference r R
      ((riemannXiDivisorZeroValue p).re - 1 / 2)
      (t - (riemannXiDivisorZeroValue p).im)) <=
        xiPairedLogTrace r t - r / R * xiPairedLogTrace R t := by
  rw [xi_compensated_resolvent_trace r R t hr hR]
  exact (xi_compensated_resolvent_summable r R t hr hR).sum_le_tsum S
    (fun p _ => (pairedResolventStrip_nonneg_iff width r R hwidth hwidthr hR).mpr hPos
      _ (hStrip p) _)

theorem zeta_multiplicity_le_positive_strip_trace {w : Complex}
    (hw : And (0 < w.re) (w.re < 1))
    (r R : Real) (hr : 1 / 2 < r) (hR : r < R)
    (width : Real) (hwidth : 0 <= width) (hwidthr : width < r)
    (hPos : 2 * width <= Real.sqrt (r ^ 2 - width ^ 2) + Real.sqrt (R ^ 2 - width ^ 2))
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= width) :
    (analyticOrderNatAt riemannZeta w : Real) * (1 / r - r / R ^ 2) <=
      xiPairedLogTrace r w.im - r / R * xiPairedLogTrace R w.im := by
  classical
  have hr0 : 0 < r := by linarith only [hr]
  have hw0 : Not (w = 0) := by
    intro h
    simp [h] at hw
  have hw1 : Not (w = 1) := by
    intro h
    simp [h] at hw
  have hAbs : abs (w.re - 1 / 2) < r := by
    apply abs_lt.mpr
    constructor <;> linarith only [hw.1, hw.2, hr]
  let f : RiemannXiDivisorZeroIndex -> Real := fun p =>
    pairedResolventDifference r R
      ((riemannXiDivisorZeroValue p).re - 1 / 2)
      (w.im - (riemannXiDivisorZeroValue p).im)
  let e := xiZeroFiberEquiv w hw0
  let j : Fin (xiZeroMultiplicity w) -> RiemannXiDivisorZeroIndex :=
    fun k => (e.symm k).val
  have hj : Function.Injective j := by
    intro a b h
    apply e.symm.injective
    exact Subtype.ext h
  have hv (k : Fin (xiZeroMultiplicity w)) :
      riemannXiDivisorZeroValue (j k) = w := (e.symm k).property
  let S : Finset RiemannXiDivisorZeroIndex := Finset.univ.image j
  have hFinite :
      (xiZeroMultiplicity w : Real) * pairedResolventDifference r R 0 0 <=
        Finset.sum S f := by
    dsimp only [S]
    rw [Finset.sum_image (fun a _ b _ h => hj h)]
    calc
      (xiZeroMultiplicity w : Real) * pairedResolventDifference r R 0 0 =
          Finset.sum Finset.univ
            (fun _ : Fin (xiZeroMultiplicity w) =>
              pairedResolventDifference r R 0 0) := by simp
      _ <= _ := by
        apply Finset.sum_le_sum
        intro k _
        change pairedResolventDifference r R 0 0 <=
          pairedResolventDifference r R
            ((riemannXiDivisorZeroValue (j k)).re - 1 / 2)
            (w.im - (riemannXiDivisorZeroValue (j k)).im)
        rw [hv, sub_self]
        exact pairedResolventDifference_same_height_min r R (w.re - 1 / 2) hAbs hR
  have hTotal := xi_compensated_resolvent_finite_mass_of_positive_strip
    width r R w.im hwidth hwidthr hr hR hPos hStrip S
  rw [<- xiZeroMultiplicity_eq_zetaOrder hw.1 hw1,
    <- pairedResolventDifference_center r R hr0 hR]
  exact hFinite.trans hTotal

def multiplicityBoundConstant (r R H L : Real) : Real :=
  r * R / (r + R) * (H + r * L)

theorem zeta_multiplicity_bound_with_constants (width r R H L : Real)
    (hwidth : 0 <= width) (hwidthr : width < r)
    (hr : 1 / 2 < r) (hR : r < R)
    (hPos : 2 * width <= Real.sqrt (r ^ 2 - width ^ 2) + Real.sqrt (R ^ 2 - width ^ 2))
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= width)
    (hHeight : forall s : Complex, 1 / 2 + r <= s.re -> s.re <= 1 / 2 + r ->
      2 <= abs s.im -> (logDeriv riemannXi s).re <= (1 / 2 : Real) * Real.log (abs s.im) + H)
    (hLip : forall s z : Complex, 1 / 2 + r <= s.re -> 1 / 2 + r <= z.re ->
      norm (logDeriv riemannXi z - logDeriv riemannXi s) <= L * norm (z - s)) :
    forall w : Complex, And (0 < w.re) (w.re < 1) -> 2 <= abs w.im ->
      (analyticOrderNatAt riemannZeta w : Real) <=
        Real.pairedResolventCoefficient r R * Real.log (abs w.im) +
          multiplicityBoundConstant r R H L := by
  let a : Real := 1 / 2 + r
  have hr0 : 0 < r := by linarith only [hr]
  have hR0 : 0 < R := hr0.trans hR
  let C : Real := multiplicityBoundConstant r R H L
  intro w hw ht
  let m : Real := (analyticOrderNatAt riemannZeta w : Real)
  let A : Real := (1 / 2 : Real) * Real.log (abs w.im) + H + r * L
  have hRe (u t : Real) : (xiResolventPoint u t).re = 1 / 2 + u := by
    simp [xiResolventPoint]
  have hIm (u t : Real) : (xiResolventPoint u t).im = t := by
    simp [xiResolventPoint]
  have hH (t : Real) (ht0 : 2 <= abs t) :
      (logDeriv riemannXi (xiResolventPoint r t)).re <=
        (1 / 2 : Real) * Real.log (abs t) + H := by
    have hh := hHeight (xiResolventPoint r t)
      (by rw [hRe]) (by rw [hRe])
      (by rw [hIm]; exact ht0)
    rwa [hIm] at hh
  have hTraceHeight : xiPairedLogTrace r w.im <=
      (1 / 2 : Real) * Real.log (abs w.im) + H := by
    have h0 := hH w.im ht
    have h1 := hH (-w.im) (by simpa using ht)
    rw [abs_neg] at h1
    dsimp only [xiPairedLogTrace]
    linarith only [h0, h1]
  have hScaled : m * (R + r) <= r * R * A := by
    have hR0 : 0 < R := hr0.trans hR
    have hDistance (t : Real) :
        norm (xiResolventPoint r t - xiResolventPoint R t) = R - r := by
      have hh : xiResolventPoint r t - xiResolventPoint R t =
          ((r - R : Real) : Complex) := by
        unfold xiResolventPoint
        push_cast
        ring
      rw [hh, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (sub_neg.mpr hR)]
      ring
    have hDifference (t : Real) :
        (logDeriv riemannXi (xiResolventPoint r t)).re -
          (logDeriv riemannXi (xiResolventPoint R t)).re <= L * (R - r) := by
      have hh := hLip (xiResolventPoint R t) (xiResolventPoint r t)
        (by rw [hRe]; linarith only [hR])
        (by rw [hRe])
      rw [hDistance] at hh
      have hReal := Complex.re_le_norm
        (logDeriv riemannXi (xiResolventPoint r t) -
          logDeriv riemannXi (xiResolventPoint R t))
      rw [Complex.sub_re] at hReal
      exact hReal.trans hh
    have hTraceDiff : xiPairedLogTrace r w.im - xiPairedLogTrace R w.im <=
        L * (R - r) := by
      have h0 := hDifference w.im
      have h1 := hDifference (-w.im)
      dsimp only [xiPairedLogTrace]
      linarith only [h0, h1]
    have hObservable : xiPairedLogTrace r w.im - r / R * xiPairedLogTrace R w.im <=
        (R - r) / R * ((1 / 2 : Real) * Real.log (abs w.im) + H) +
          (r / R) * L * (R - r) := by
      have h0 := mul_le_mul_of_nonneg_left hTraceHeight
        (div_nonneg (sub_nonneg.mpr hR.le) hR0.le)
      have h1 := mul_le_mul_of_nonneg_left hTraceDiff (div_nonneg hr0.le hR0.le)
      have hIdentity : xiPairedLogTrace r w.im - r / R * xiPairedLogTrace R w.im =
          (R - r) / R * xiPairedLogTrace r w.im +
            (r / R) * (xiPairedLogTrace r w.im - xiPairedLogTrace R w.im) := by
        field_simp [hR0.ne']
        ring
      rw [hIdentity]
      nlinarith only [h0, h1]
    have hRaw := (zeta_multiplicity_le_positive_strip_trace hw r R hr hR
      width hwidth hwidthr hPos hStrip).trans
      hObservable
    change m * (1 / r - r / R ^ 2) <= _ at hRaw
    have hFactor : 0 <= r * R ^ 2 / (R - r) :=
      div_nonneg (mul_nonneg hr0.le (sq_nonneg R)) (sub_nonneg.mpr hR.le)
    have hMult := mul_le_mul_of_nonneg_right hRaw hFactor
    dsimp only [A]
    convert hMult using 1 <;>
      field_simp [hr0.ne', hR0.ne', (sub_pos.mpr hR).ne'] <;> ring
  have hDiv := mul_le_mul_of_nonneg_right hScaled
    (div_nonneg (by norm_num : (0 : Real) <= 1) (add_nonneg hR0.le hr0.le))
  have hRaw : m <= r * R / (r + R) * A := by
    convert hDiv using 1 <;>
      field_simp [(add_pos hr0 hR0).ne', (add_pos hR0 hr0).ne'] <;> ring
  have hExpand : r * R / (r + R) * A =
      Real.pairedResolventCoefficient r R * Real.log (abs w.im) +
        r * R / (r + R) * (H + r * L) := by
    dsimp only [A, Real.pairedResolventCoefficient]
    field_simp [(add_pos hr0 hR0).ne']
    ring
  rw [hExpand] at hRaw
  change m <= Real.pairedResolventCoefficient r R * Real.log (abs w.im) + C
  simpa only [C, multiplicityBoundConstant] using hRaw

theorem zeta_multiplicity_log_bound_of_positive_strip (width r R : Real)
    (hwidth : 0 <= width) (hwidthr : width < r)
    (hr : 1 / 2 < r) (hR : r < R)
    (hPos : 2 * width <= Real.sqrt (r ^ 2 - width ^ 2) + Real.sqrt (R ^ 2 - width ^ 2))
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= width) :
    Exists (fun C : Real => And (0 <= C)
      (forall w : Complex, And (0 < w.re) (w.re < 1) -> 2 <= abs w.im ->
        (analyticOrderNatAt riemannZeta w : Real) <=
          Real.pairedResolventCoefficient r R * Real.log (abs w.im) + C)) := by
  let a : Real := 1 / 2 + r
  have hr0 : 0 < r := by linarith only [hr]
  have hR0 : 0 < R := hr0.trans hR
  have ha : 1 < a := by dsimp only [a]; linarith only [hr]
  choose H hH hHeight using xi_logDeriv_height_upper a a ha
  choose L hL hLip using xi_logDeriv_uniform_lipschitz a ha
  let C : Real := multiplicityBoundConstant r R H L
  have hC : 0 <= C := by dsimp only [C, multiplicityBoundConstant]; positivity
  refine Exists.intro C (And.intro hC ?_)
  exact zeta_multiplicity_bound_with_constants width r R H L hwidth hwidthr hr hR
    hPos hStrip hHeight hLip

end PrimeFactorOscillations
