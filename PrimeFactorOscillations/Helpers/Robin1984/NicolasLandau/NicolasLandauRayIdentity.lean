/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauRightmostRay.lean
Original source lines 356-494. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauRayTransport

/-!
# Identification of the transform along the rightmost-zero ray

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

def nicolasRightmostRayPoint (rho : Complex) (eps : Real) : Complex :=
  (1 - rho) - (eps : Complex)

theorem nicolasLandauPositiveComplexContinuationFilled_analyticAt_rightmostRay
    {X b : Real} (hX : 3 <= X) {rho : Complex}
    (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex
      (nicolasLandauPositiveComplexContinuationFilled X b)
      (nicolasRightmostRayPoint rho eps) := by
  have hJ := nicolasJShiftedComplexContinuationFilled_analyticAt_rightmostRay
    hZero hHalf hOne hRay hEps
  have hStartup := nicolasJComplexMellinStartup_analyticAt hX
    (nicolasRightmostRayPoint rho eps)
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOne
  have hPointIm : (nicolasRightmostRayPoint rho eps).im = -rho.im := by
    unfold nicolasRightmostRayPoint
    simp
  have hPointNeB : Not (nicolasRightmostRayPoint rho eps = (b : Complex)) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hPointIm, Complex.ofReal_im] at hEqIm
    exact hIm (neg_eq_zero.mp hEqIm)
  have hRpow := nicolasLandauRpowComplexContinuation_analyticAt
    (lt_of_lt_of_le (by norm_num) hX) hPointNeB
  unfold nicolasLandauPositiveComplexContinuationFilled
  exact (hJ.sub hStartup).add hRpow

theorem nicolasLandauComplexMGF_analyticAt_rightmostRay
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    {rho : Complex} (hHalf : (1 / 2 : Real) < rho.re)
    (hLower : 1 - rho.re < b)
    {eps : Real} (hEps : 0 <= eps) :
    AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b))
      (nicolasRightmostRayPoint rho eps) := by
  apply nicolasLandauComplexMGF_analyticAt_of_positive
    hX hb hbHalf hPos
  unfold nicolasRightmostRayPoint
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  linarith [hLower]

theorem nicolasLandauComplexMGF_rightmostRay_analyticAt_real
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    {rho : Complex} (hHalf : (1 / 2 : Real) < rho.re)
    (hLower : 1 - rho.re < b)
    {eps : Real} (hEps : 0 <= eps) :
    AnalyticAt Real (fun e : Real =>
      complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b)
        (nicolasRightmostRayPoint rho e)) eps := by
  have hOuterComplex := nicolasLandauComplexMGF_analyticAt_rightmostRay
    hX hb hbHalf hPos hHalf hLower hEps
  have hOuterReal : AnalyticAt Real
      (complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b))
      (nicolasRightmostRayPoint rho eps) := hOuterComplex.restrictScalars
  have hInner : AnalyticAt Real (nicolasRightmostRayPoint rho) eps := by
    unfold nicolasRightmostRayPoint
    exact analyticAt_const.sub (Complex.ofRealCLM.analyticAt eps)
  exact hOuterReal.comp_of_eq hInner rfl

theorem nicolasLandauPositiveComplexContinuationFilled_rightmostRay_analyticAt_real
    {X b : Real} (hX : 3 <= X) {rho : Complex}
    (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Real (fun e : Real =>
      nicolasLandauPositiveComplexContinuationFilled X b
        (nicolasRightmostRayPoint rho e)) eps := by
  have hOuterComplex :=
    nicolasLandauPositiveComplexContinuationFilled_analyticAt_rightmostRay
      (b := b) hX hZero hHalf hOne hRay hEps
  have hOuterReal : AnalyticAt Real
      (nicolasLandauPositiveComplexContinuationFilled X b)
      (nicolasRightmostRayPoint rho eps) := hOuterComplex.restrictScalars
  have hInner : AnalyticAt Real (nicolasRightmostRayPoint rho) eps := by
    unfold nicolasRightmostRayPoint
    exact analyticAt_const.sub (Complex.ofRealCLM.analyticAt eps)
  exact hOuterReal.comp_of_eq hInner rfl

theorem nicolasLandauComplexMGF_eq_continuationFilled_rightmostRay
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hLower : 1 - rho.re < b)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b)
        (nicolasRightmostRayPoint rho eps) =
      nicolasLandauPositiveComplexContinuationFilled X b
        (nicolasRightmostRayPoint rho eps) := by
  let F : Real -> Complex := fun e : Real =>
    complexMGF (fun x : Real => Real.log x)
      (nicolasLandauPositiveMeasure X b)
      (nicolasRightmostRayPoint rho e)
  let G : Real -> Complex := fun e : Real =>
    nicolasLandauPositiveComplexContinuationFilled X b
      (nicolasRightmostRayPoint rho e)
  have hF : AnalyticOnNhd Real F (Ioi (0 : Real)) := by
    intro e he
    dsimp [F]
    exact nicolasLandauComplexMGF_rightmostRay_analyticAt_real
      hX hb hbHalf hPos hHalf hLower (mem_Ioi.mp he).le
  have hG : AnalyticOnNhd Real G (Ioi (0 : Real)) := by
    intro e he
    dsimp [G]
    exact
      nicolasLandauPositiveComplexContinuationFilled_rightmostRay_analyticAt_real
        hX hZero hHalf hOne hRay (mem_Ioi.mp he)
  have hEqNhd : Filter.EventuallyEq (nhds (2 : Real)) F G := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (1 : Real) < 2)] with e he
    dsimp [F, G]
    apply nicolasLandauComplexMGF_eq_continuationFilled_of_re_neg
      hX hb hPos
    unfold nicolasRightmostRayPoint
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith [mem_Ioi.mp he]
  have hEqOn : EqOn F G (Ioi (0 : Real)) :=
    hF.eqOn_of_preconnected_of_eventuallyEq hG
      (convex_Ioi (0 : Real)).isPreconnected (by norm_num) hEqNhd
  exact hEqOn hEps

end

end Robin1984
