/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauRightmostRay.lean
Original source lines 1506-1586. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauRayGrowth

/-!
# The canonical negative excursion consequence of false RH

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem exists_nicolasJ_omegaMinus_of_riemannZeta_zero_re_gt_half
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Exists fun b : Real => And (0 < b) (And (b < 1 / 2)
      (AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b)))) := by
  choose rhoMax hMaxZero hMaxHalf hMaxOne hMaxIm hRay using
    exists_rightmost_horizontal_riemannZeta_zero
      hZero hHalf hOneRe
  let b : Real := ((1 - rhoMax.re) + 1 / 2) / 2
  have hbPos : 0 < b := by
    dsimp [b]
    linarith
  have hbLower : 1 - rhoMax.re < b := by
    dsimp [b]
    linarith
  have hbHalf : b < 1 / 2 := by
    dsimp [b]
    linarith
  refine Exists.intro b (And.intro hbPos (And.intro hbHalf ?_))
  by_contra hNot
  choose X hX hPos hAnalytic using
    exists_nicolasLandauComplexMGF_analytic_halfPlane_of_not_omegaMinus
      hbPos hbHalf.le hNot
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let MGF : Real -> Complex := fun eps =>
    complexMGF (fun x : Real => Real.log x)
      (nicolasLandauPositiveMeasure X b)
      (nicolasRightmostRayPoint rhoMax eps)
  let P : Real -> Complex := fun eps =>
    nicolasLandauPositiveComplexContinuationFilled X b
      (nicolasRightmostRayPoint rhoMax eps)
  have hPointRe : (nicolasRightmostRayPoint rhoMax 0).re =
      1 - rhoMax.re := by
    unfold nicolasRightmostRayPoint
    simp
  have hMGFAnalytic : AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b))
      (nicolasRightmostRayPoint rhoMax 0) := by
    apply hAnalytic
    rw [hPointRe]
    exact hbLower
  let MGF0 : Complex := complexMGF (fun x : Real => Real.log x)
    (nicolasLandauPositiveMeasure X b)
    (nicolasRightmostRayPoint rhoMax 0)
  have hInner : Tendsto (nicolasRightmostRayPoint rhoMax) l
      (nhds (nicolasRightmostRayPoint rhoMax 0)) := by
    have hContinuous : ContinuousAt (nicolasRightmostRayPoint rhoMax) 0 := by
      unfold nicolasRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hMGF : Tendsto MGF l (nhds MGF0) := by
    have hComp := hMGFAnalytic.continuousAt.tendsto.comp hInner
    simpa [MGF, MGF0, Function.comp_def] using hComp
  have hEq : Filter.Eventually (fun eps : Real => MGF eps = P eps) l := by
    filter_upwards [self_mem_nhdsWithin] with eps hEps
    dsimp [MGF, P]
    exact nicolasLandauComplexMGF_eq_continuationFilled_rightmostRay
      hX hbPos hbHalf.le hPos hMaxZero hMaxHalf hMaxOne hbLower hRay
      (mem_Ioi.mp hEps)
  have hPNormFinite : Tendsto (fun eps : Real => norm (P eps)) l
      (nhds (norm MGF0)) := by
    have hMGFNorm := hMGF.norm
    apply hMGFNorm.congr'
    filter_upwards [hEq] with eps hAt
    rw [hAt]
  have hPNormTop : Tendsto (fun eps : Real => norm (P eps)) l atTop := by
    simpa [l, P] using
      nicolasLandauPositiveComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
        hX hMaxZero hMaxHalf hMaxOne hRay
  exact not_tendsto_nhds_of_tendsto_atTop hPNormTop (norm MGF0) hPNormFinite

theorem exists_nicolasJ_omegaMinus_of_not_riemannHypothesis
    (hNotRH : Not RiemannHypothesis) :
    Exists fun b : Real => And (0 < b) (And (b < 1 / 2)
      (AtTopOmegaMinus nicolasJ (fun x : Real => x ^ (-b)))) := by
  choose rho hZero hHalf hOneRe using
    exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
  exact exists_nicolasJ_omegaMinus_of_riemannZeta_zero_re_gt_half
    hZero hHalf hOneRe

end

end Robin1984
