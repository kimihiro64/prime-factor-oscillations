/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasZetaStrip
import PrimeFactorOscillations.Helpers.QRHSevenEighths
import PrimeFactorOscillations.Helpers.XiPairedResolventTrace
import PrimeFactorOscillations.Helpers.XiVerticalLogDerivative
import PrimeFactorOscillations.Helpers.XiZetaMultiplicity

/-!
# QRH strip control of localized multiplicity mass

The installed seven-eighths theorem makes the complete compensated
reflected resolvent nonnegative. Every multiplicity copy of the chosen
zero is charged before the other nonnegative terms are discarded.
The resulting observable still contains all four xi logarithmic derivatives.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Complex Robin1984

theorem xi_compensated_qrh_strip (r : Real) (hr : 1 / 2 < r)
    (hsq : 9 / 32 <= r ^ 2) (p : RiemannXiDivisorZeroIndex) :
    And (abs ((riemannXiDivisorZeroValue p).re - 1 / 2) < r)
      (2 * ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2 <= r ^ 2) := by
  have hp := canonical_xi_strip_of_zeta_nonvanishing
    (by norm_num : (0 : Real) <= 7 / 8)
    (fun s hs _ => QRH.zeta_ne_zero s hs) p
  have hAbs : abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8 := by
    apply abs_le.mpr
    constructor <;> linarith only [hp.1, hp.2]
  constructor
  . exact hAbs.trans_lt (by linarith only [hr])
  . have hx := abs_le.mp hAbs
    have hh := mul_nonneg
      (show 0 <= 3 / 8 - ((riemannXiDivisorZeroValue p).re - 1 / 2) by
        linarith only [hx.2])
      (show 0 <= 3 / 8 + ((riemannXiDivisorZeroValue p).re - 1 / 2) by
        linarith only [hx.1])
    nlinarith only [hh, hsq]

theorem zeta_multiplicity_le_compensated_xi_trace {w : Complex}
    (hw : And (0 < w.re) (w.re < 1))
    (r R : Real) (hr : 1 / 2 < r) (hR : r < R)
    (hsq : 9 / 32 <= r ^ 2) :
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
  have hTotal := xi_compensated_resolvent_finite_mass r R w.im hr hR
    (xi_compensated_qrh_strip r hr hsq) S
  rw [<- xiZeroMultiplicity_eq_zetaOrder hw.1 hw1,
    <- pairedResolventDifference_center r R hr0 hR]
  exact hFinite.trans hTotal

theorem zeta_multiplicity_log_bound_of_strip_radius (r : Real)
    (hr : 1 / 2 < r) (hsq : 9 / 32 <= r ^ 2) :
    Exists (fun C : Real => And (0 <= C)
      (forall w : Complex, And (0 < w.re) (w.re < 1) -> 2 <= abs w.im ->
        (analyticOrderNatAt riemannZeta w : Real) <=
          r / 4 * Real.log (abs w.im) + C)) := by
  let a : Real := 1 / 2 + r
  have hr0 : 0 < r := by linarith only [hr]
  have ha : 1 < a := by dsimp only [a]; linarith only [hr]
  choose C0 hC0 hHeight using xi_logDeriv_height_upper a a ha
  choose L hL hLip using xi_logDeriv_uniform_lipschitz a ha
  let C : Real := r / 2 * C0 + r ^ 2 / 2 * L + 1
  have hC : 0 <= C := by dsimp only [C]; positivity
  refine Exists.intro C (And.intro hC ?_)
  intro w hw ht
  let m : Real := (analyticOrderNatAt riemannZeta w : Real)
  let A : Real := (1 / 2 : Real) * Real.log (abs w.im) + C0 + r * L
  have hRe (u t : Real) : (xiResolventPoint u t).re = 1 / 2 + u := by
    simp [xiResolventPoint]
  have hIm (u t : Real) : (xiResolventPoint u t).im = t := by
    simp [xiResolventPoint]
  have hH (t : Real) (ht0 : 2 <= abs t) :
      (logDeriv riemannXi (xiResolventPoint r t)).re <=
        (1 / 2 : Real) * Real.log (abs t) + C0 := by
    have hh := hHeight (xiResolventPoint r t)
      (by rw [hRe]) (by rw [hRe])
      (by rw [hIm]; exact ht0)
    rwa [hIm] at hh
  have hTraceHeight : xiPairedLogTrace r w.im <=
      (1 / 2 : Real) * Real.log (abs w.im) + C0 := by
    have h0 := hH w.im ht
    have h1 := hH (-w.im) (by simpa using ht)
    rw [abs_neg] at h1
    dsimp only [xiPairedLogTrace]
    linarith only [h0, h1]
  have hExpanded (R : Real) (hR : r < R) :
      m * (R + r) <= r * R * A := by
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
        (by rw [hRe]; dsimp only [a]; linarith only [hR])
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
        (R - r) / R * ((1 / 2 : Real) * Real.log (abs w.im) + C0) +
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
    have hRaw := (zeta_multiplicity_le_compensated_xi_trace hw r R hr hR hsq).trans
      hObservable
    change m * (1 / r - r / R ^ 2) <= _ at hRaw
    have hFactor : 0 <= r * R ^ 2 / (R - r) :=
      div_nonneg (mul_nonneg hr0.le (sq_nonneg R)) (sub_nonneg.mpr hR.le)
    have hMult := mul_le_mul_of_nonneg_right hRaw hFactor
    dsimp only [A]
    convert hMult using 1 <;>
      field_simp [hr0.ne', hR0.ne', (sub_pos.mpr hR).ne'] <;> ring
  have hContLeft : Continuous (fun R : Real => m * (R + r)) :=
    continuous_const.mul (continuous_id.add continuous_const)
  have hContRight : Continuous (fun R : Real => r * R * A) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hNear : Filter.Eventually (fun R : Real => m * (R + r) <= r * R * A)
      (nhdsWithin r (Set.Ioi r)) := by
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro R hR
    exact hExpanded R hR
  have hEnd : m * (r + r) <= r * r * A :=
    le_of_tendsto_of_tendsto
      (hContLeft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hContRight.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hNear
  change m <= r / 4 * Real.log (abs w.im) + C
  by_contra hn
  have hm := lt_of_not_ge hn
  have hh := mul_pos (sub_pos.mpr hm) hr0
  dsimp only [C, A] at hh hEnd
  nlinarith only [hh, hEnd, hr0]

theorem zeta_multiplicity_seven_eighths_log_bound :
    Exists (fun C : Real => And (0 < C)
      (forall w : Complex, And (0 < w.re) (w.re < 1) -> 2 <= abs w.im ->
        (analyticOrderNatAt riemannZeta w : Real) <=
          (3 * Real.sqrt 2 / 32) * Real.log (abs w.im) + C)) := by
  let r : Real := 3 * Real.sqrt 2 / 8
  have hSqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hSquare : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : 1 / 2 < r := by
    dsimp only [r]
    nlinarith only [hSquare, hSqrt]
  have hsq : 9 / 32 <= r ^ 2 := by
    dsimp only [r]
    nlinarith only [hSquare]
  choose C hC hBound using zeta_multiplicity_log_bound_of_strip_radius r hr hsq
  refine Exists.intro (C + 1) (And.intro (by linarith only [hC]) ?_)
  intro w hw ht
  have hh := hBound w hw ht
  have hCoefficient : r / 4 = 3 * Real.sqrt 2 / 32 := by
    dsimp only [r]
    ring
  rw [hCoefficient] at hh
  linarith only [hh]

end PrimeFactorOscillations
