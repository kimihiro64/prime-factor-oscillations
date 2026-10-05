/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasReflectedContinuation

/-!
# Positive Nicolas J excursions under failure of RH

The reflected Mellin transform cannot remain nonnegative past a cutoff:
a zero to the right of the critical line forces a singular endpoint.
Consequently J exceeds every prescribed square-root-scale amplitude
arbitrarily far out under failure of RH.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter MeasureTheory ProbabilityTheory Set Robin1984
open scoped ENNReal Topology

noncomputable section

theorem nicolasReflectedComplexContinuation_analyticAt_rightmostRay
    {X A b : Real} (hX : 3 <= X) {rho : Complex}
    (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex (nicolasReflectedComplexContinuation X A b)
      (nicolasRightmostRayPoint rho eps) := by
  have hPlus := nicolasLandauPositiveComplexContinuationFilled_analyticAt_rightmostRay
    (b := b) hX hZero hHalf hOne hRay hEps
  have hIm := riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
    (lt_trans (by norm_num) hHalf) hOne
  have hPointNeB : Not (nicolasRightmostRayPoint rho eps = (b : Complex)) := by
    intro hEq
    have hi := congrArg Complex.im hEq
    unfold nicolasRightmostRayPoint at hi
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im] at hi
    apply hIm
    linarith
  have hPower := nicolasLandauRpowComplexContinuation_analyticAt
    (lt_of_lt_of_le (by norm_num) hX) hPointNeB
  unfold nicolasReflectedComplexContinuation
  exact (analyticAt_const.mul hPower).sub hPlus

theorem nicolasReflectedComplexMGF_rightmostRay_analyticAt_real
    {X A b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x -> 0 <= nicolasReflectedTail A b x)
    {rho : Complex} (hLower : 1 - rho.re < b)
    {eps : Real} (hEps : 0 <= eps) :
    AnalyticAt Real (fun e : Real =>
      complexMGF (fun x : Real => Real.log x) (nicolasReflectedMeasure X A b)
        (nicolasRightmostRayPoint rho e)) eps := by
  have hRe : (nicolasRightmostRayPoint rho eps).re < b := by
    unfold nicolasRightmostRayPoint
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hOuterComplex := nicolasReflectedComplexMGF_analyticAt hX hb hbHalf hPos hRe
  have hOuterReal : AnalyticAt Real
      (complexMGF (fun x : Real => Real.log x) (nicolasReflectedMeasure X A b))
      (nicolasRightmostRayPoint rho eps) := hOuterComplex.restrictScalars
  have hInner : AnalyticAt Real (nicolasRightmostRayPoint rho) eps := by
    unfold nicolasRightmostRayPoint
    exact analyticAt_const.sub (Complex.ofRealCLM.analyticAt eps)
  exact hOuterReal.comp_of_eq hInner rfl

theorem nicolasReflectedComplexContinuation_rightmostRay_analyticAt_real
    {X A b : Real} (hX : 3 <= X) {rho : Complex}
    (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Real (fun e : Real =>
      nicolasReflectedComplexContinuation X A b (nicolasRightmostRayPoint rho e)) eps := by
  have hOuterComplex := nicolasReflectedComplexContinuation_analyticAt_rightmostRay
    (A := A) (b := b) hX hZero hHalf hOne hRay hEps
  have hOuterReal : AnalyticAt Real (nicolasReflectedComplexContinuation X A b)
      (nicolasRightmostRayPoint rho eps) := hOuterComplex.restrictScalars
  have hInner : AnalyticAt Real (nicolasRightmostRayPoint rho) eps := by
    unfold nicolasRightmostRayPoint
    exact analyticAt_const.sub (Complex.ofRealCLM.analyticAt eps)
  exact hOuterReal.comp_of_eq hInner rfl

theorem nicolasReflectedComplexMGF_eq_continuation_rightmostRay
    {X A b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x -> 0 <= nicolasReflectedTail A b x)
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hLower : 1 - rho.re < b)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    complexMGF (fun x : Real => Real.log x) (nicolasReflectedMeasure X A b)
        (nicolasRightmostRayPoint rho eps) =
      nicolasReflectedComplexContinuation X A b (nicolasRightmostRayPoint rho eps) := by
  let F : Real -> Complex := fun e =>
    complexMGF (fun x : Real => Real.log x) (nicolasReflectedMeasure X A b)
      (nicolasRightmostRayPoint rho e)
  let G : Real -> Complex := fun e =>
    nicolasReflectedComplexContinuation X A b (nicolasRightmostRayPoint rho e)
  have hF : AnalyticOnNhd Real F (Ioi (0 : Real)) := by
    intro e he
    exact nicolasReflectedComplexMGF_rightmostRay_analyticAt_real
      hX hb hbHalf hPos hLower (mem_Ioi.mp he).le
  have hG : AnalyticOnNhd Real G (Ioi (0 : Real)) := by
    intro e he
    exact nicolasReflectedComplexContinuation_rightmostRay_analyticAt_real
      hX hZero hHalf hOne hRay (mem_Ioi.mp he)
  have hEqNhd : Filter.EventuallyEq (nhds (2 : Real)) F G := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (1 : Real) < 2)] with e he
    dsimp [F, G]
    apply nicolasReflectedComplexMGF_eq_continuation_of_re_neg hX hb hPos
    unfold nicolasRightmostRayPoint
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith [mem_Ioi.mp he]
  have hEqOn : EqOn F G (Ioi (0 : Real)) :=
    hF.eqOn_of_preconnected_of_eventuallyEq hG
      (convex_Ioi (0 : Real)).isPreconnected (by norm_num) hEqNhd
  exact hEqOn hEps

theorem nicolasReflectedComplexContinuation_rightmostRay_norm_tendsto_atTop
    {X A b : Real} (hX : 3 <= X) {rho : Complex}
    (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
      norm (nicolasReflectedComplexContinuation X A b (nicolasRightmostRayPoint rho eps)))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let J : Real -> Complex := fun eps =>
    -nicolasLandauPositiveComplexContinuationFilled X b (nicolasRightmostRayPoint rho eps)
  let D : Real -> Complex := fun eps =>
    ((A + 1 : Real) : Complex) *
      nicolasLandauRpowComplexContinuation X b (nicolasRightmostRayPoint rho eps)
  let P : Real -> Complex := fun eps =>
    nicolasReflectedComplexContinuation X A b (nicolasRightmostRayPoint rho eps)
  have hJ : Tendsto (fun eps : Real => norm (J eps)) l atTop := by
    simpa [l, J] using
      nicolasLandauPositiveComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
        (b := b) hX hZero hHalf hOne hRay
  have hIm := riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
    (lt_trans (by norm_num) hHalf) hOne
  have hPointNeB : Not (nicolasRightmostRayPoint rho 0 = (b : Complex)) := by
    intro hEq
    have hi := congrArg Complex.im hEq
    unfold nicolasRightmostRayPoint at hi
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im] at hi
    apply hIm
    linarith
  have hCorrectionAnalytic : AnalyticAt Complex (fun z : Complex =>
      ((A + 1 : Real) : Complex) * nicolasLandauRpowComplexContinuation X b z)
      (nicolasRightmostRayPoint rho 0) :=
    analyticAt_const.mul (nicolasLandauRpowComplexContinuation_analyticAt
      (lt_of_lt_of_le (by norm_num) hX) hPointNeB)
  let D0 : Complex := ((A + 1 : Real) : Complex) *
    nicolasLandauRpowComplexContinuation X b (nicolasRightmostRayPoint rho 0)
  have hInner : Tendsto (nicolasRightmostRayPoint rho) l
      (nhds (nicolasRightmostRayPoint rho 0)) := by
    have hContinuous : ContinuousAt (nicolasRightmostRayPoint rho) 0 := by
      unfold nicolasRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hD : Tendsto D l (nhds D0) := by
    simpa [D, D0, Function.comp_def] using
      hCorrectionAnalytic.continuousAt.tendsto.comp hInner
  have hDBound : Filter.Eventually (fun eps : Real => norm (D eps) <= norm D0 + 1) l := by
    have hBall := hD.eventually
      (Metric.ball_mem_nhds D0 (by norm_num : (0 : Real) < 1))
    filter_upwards [hBall] with eps he
    have hDist : norm (D eps - D0) < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using he
    calc
      norm (D eps) = norm ((D eps - D0) + D0) := by ring_nf
      _ <= norm (D eps - D0) + norm D0 := norm_add_le _ _
      _ <= norm D0 + 1 := by linarith
  have hEq : forall eps : Real, P eps = J eps + D eps := by
    intro eps
    unfold P J D nicolasReflectedComplexContinuation
    ring
  have hLowerTendsto : Tendsto
      (fun eps : Real => norm (J eps) - (norm D0 + 1)) l atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right l (-(norm D0 + 1)) hJ)
  have hEventualLower : Filter.Eventually
      (fun eps : Real => norm (J eps) - (norm D0 + 1) <= norm (P eps)) l := by
    filter_upwards [hDBound] with eps hBound
    have hTriangle : norm (J eps) <= norm (P eps) + norm (D eps) := by
      calc
        norm (J eps) = norm ((J eps + D eps) - D eps) := by ring_nf
        _ = norm (P eps - D eps) := by rw [hEq]
        _ <= norm (P eps) + norm (D eps) := norm_sub_le _ _
    linarith
  exact tendsto_atTop_mono' l hEventualLower hLowerTendsto

theorem nicolasReflectedTail_not_nonneg_of_rightmost_zero
    {X A b : Real} (hX : 3 <= X) {rho : Complex}
    (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    (hPos : forall x : Real, X < x -> 0 <= nicolasReflectedTail A b x) : False := by
  have hb : 0 < b := by linarith
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let MGF : Real -> Complex := fun eps =>
    complexMGF (fun x : Real => Real.log x) (nicolasReflectedMeasure X A b)
      (nicolasRightmostRayPoint rho eps)
  let P : Real -> Complex := fun eps =>
    nicolasReflectedComplexContinuation X A b (nicolasRightmostRayPoint rho eps)
  have hPointRe : (nicolasRightmostRayPoint rho 0).re = 1 - rho.re := by
    unfold nicolasRightmostRayPoint
    simp
  have hMGFAnalytic : AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x) (nicolasReflectedMeasure X A b))
      (nicolasRightmostRayPoint rho 0) := by
    apply nicolasReflectedComplexMGF_analyticAt hX hb hbHalf hPos
    rw [hPointRe]
    exact hLower
  let MGF0 : Complex := complexMGF (fun x : Real => Real.log x)
    (nicolasReflectedMeasure X A b) (nicolasRightmostRayPoint rho 0)
  have hInner : Tendsto (nicolasRightmostRayPoint rho) l
      (nhds (nicolasRightmostRayPoint rho 0)) := by
    have hContinuous : ContinuousAt (nicolasRightmostRayPoint rho) 0 := by
      unfold nicolasRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hMGF : Tendsto MGF l (nhds MGF0) := by
    simpa [MGF, MGF0, Function.comp_def] using
      hMGFAnalytic.continuousAt.tendsto.comp hInner
  have hEq : Filter.Eventually (fun eps : Real => MGF eps = P eps) l := by
    filter_upwards [self_mem_nhdsWithin] with eps he
    exact nicolasReflectedComplexMGF_eq_continuation_rightmostRay
      hX hb hbHalf hPos hZero hHalf hOne hLower hRay (mem_Ioi.mp he)
  have hPNormFinite : Tendsto (fun eps : Real => norm (P eps)) l (nhds (norm MGF0)) := by
    apply hMGF.norm.congr'
    filter_upwards [hEq] with eps he
    rw [he]
  have hPNormTop : Tendsto (fun eps : Real => norm (P eps)) l atTop := by
    simpa [l, P] using
      nicolasReflectedComplexContinuation_rightmostRay_norm_tendsto_atTop
        (A := A) (b := b) hX hZero hHalf hOne hRay
  exact not_tendsto_nhds_of_tendsto_atTop hPNormTop (norm MGF0) hPNormFinite

theorem nicolasJ_arbitrary_positive_excursions_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2) :
    forall X A : Real, exists x : Real,
      max X 3 < x /\ A * x ^ (-b) < nicolasJ x := by
  choose rhoMax hMaxZero hMaxHalf hMaxOne hMaxIm hRay using
    exists_rightmost_horizontal_riemannZeta_zero hZero hHalf hOne
  have hRe : rho.re <= rhoMax.re := by
    apply le_of_not_gt
    intro hlt
    have hv : 0 < rho.re - rhoMax.re := sub_pos.mpr hlt
    have hShift : rhoMax + ((rho.re - rhoMax.re : Real) : Complex) = rho := by
      apply Complex.ext
      . simp only [Complex.add_re, Complex.ofReal_re]
        ring
      . simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hMaxIm
    apply hRay (rho.re - rhoMax.re) hv
    rw [hShift]
    exact hZero
  intro X A
  by_contra hNo
  have hPos : forall x : Real, max X 3 < x -> 0 <= nicolasReflectedTail A b x := by
    intro x hx
    have hle : nicolasJ x <= A * x ^ (-b) := by
      apply le_of_not_gt
      intro hlt
      exact hNo (Exists.intro x (And.intro hx hlt))
    unfold nicolasReflectedTail
    exact sub_nonneg.mpr hle
  exact nicolasReflectedTail_not_nonneg_of_rightmost_zero
    (le_max_right X 3) hMaxZero hMaxHalf hMaxOne
    (by linarith) hbHalf hRay hPos

theorem nicolasJ_arbitrary_positive_half_excursions_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1) :
    forall X A : Real, exists x : Real,
      max X 3 < x /\ A * x ^ (-(1 / 2 : Real)) < nicolasJ x :=
  nicolasJ_arbitrary_positive_excursions_of_zero hZero hHalf hOne
    (by linarith) (by norm_num)

theorem nicolasJ_arbitrary_positive_half_excursions_of_not_RH
    (hNotRH : Not RiemannHypothesis) :
    forall X A : Real, exists x : Real,
      max X 3 < x /\ A * x ^ (-(1 / 2 : Real)) < nicolasJ x := by
  choose rho hZero hHalf hOne using
    exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
  exact nicolasJ_arbitrary_positive_half_excursions_of_zero hZero hHalf hOne

end

end PrimeFactorOscillations
