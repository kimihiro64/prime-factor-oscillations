/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauComplexFrontier.lean
Original source lines 1072-1307. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauComplexLarge

/-!
# The full Nicolas continuation along the rightmost-zero ray

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_large_of_geometry
    {d : Real} (hd : 0 < d) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) (hzNorm : d <= norm z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hzNe : Not (z = 0) := by
    intro hEq
    rw [hEq, norm_zero] at hzNorm
    linarith
  have hContinuous : ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
    intro u hu
    have hsRe : 1 < ((((u + 1 : Real) : Complex) - z).re) := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [hzRe, mem_Ioi.mp hu]
    have hsZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hsOne : Not ((((u + 1 : Real) : Complex) - z) = 1) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hZeta : Not (riemannZeta
        (((u + 1 : Real) : Complex) - z) = 0) :=
      riemannZeta_ne_zero_of_one_lt_re hsRe
    have hFactor : Not (nicolasZetaPoleFactor
        (((u + 1 : Real) : Complex) - z) = 0) :=
      nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      (by linarith [mem_Ioi.mp hu] : 0 <= u) hzNe hsZero hFactor
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        nicolasJMellinShiftIntegrandFilled z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  apply Integrable.mono'
    (nicolasJLargeMajorantAtDistance_integrableOn hd)
    (hContinuous.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_nicolasJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge
    hd hu hzRe hzNorm

theorem exists_nicolasRightmostRayLargeGeometry
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {eps : Real} (hEps : 0 < eps) :
    Exists fun d : Real => Exists fun R : Real =>
      And (0 < d) (And (0 < R)
        (forall z : Complex,
          Membership.mem
            (Metric.ball ((1 - rho) - (eps : Complex)) R) z ->
            And (z.re <= (3 / 4 : Real)) (d <= norm z))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOne
  have hCenterIm : center.im = -rho.im := by
    dsimp [center]
    simp
  have hCenterNe : Not (center = 0) := by
    intro hEq
    have hZeroIm : center.im = 0 := by rw [hEq]; simp
    exact hIm (neg_eq_zero.mp (hCenterIm.symm.trans hZeroIm))
  have hCenterNorm : 0 < norm center := norm_pos_iff.mpr hCenterNe
  have hCenterRe : center.re = 1 - rho.re - eps := by
    dsimp [center]
  have hReMargin : 0 < (3 / 4 : Real) - center.re := by
    rw [hCenterRe]
    linarith
  let d : Real := norm center / 2
  let R : Real := min (norm center / 2)
    (((3 / 4 : Real) - center.re) / 2)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hRPos : 0 < R := by
    dsimp [R]
    exact lt_min (by positivity) (by positivity)
  have hGeometry : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (z.re <= (3 / 4 : Real)) (d <= norm z) := by
    intro z hz
    have hzDist : dist z center < R := by
      simpa [Metric.mem_ball] using hz
    have hDistNorm : dist z center < norm center / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_left _ _)
    have hDistRe : dist z center <
        ((3 / 4 : Real) - center.re) / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_right _ _)
    have hReDiff : z.re - center.re <= dist z center := by
      calc
        z.re - center.re <= abs (z.re - center.re) := le_abs_self _
        _ = abs ((z - center).re) :=
          congrArg abs (Complex.sub_re z center).symm
        _ <= norm (z - center) := Complex.abs_re_le_norm _
        _ = dist z center := by rw [dist_eq_norm]
    have hTriangle : norm center <= dist center z + norm z := by
      have h := dist_triangle center z 0
      simpa [dist_zero_right] using h
    have hNorm : d <= norm z := by
      dsimp [d]
      rw [dist_comm center z] at hTriangle
      linarith
    exact And.intro (by linarith) hNorm
  exact Exists.intro d (Exists.intro R
    (And.intro hd (And.intro hRPos (by simpa [center] using hGeometry))))

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      ((1 - rho) - (eps : Complex)) := by
  choose d R hd hRPos hGeometry using
    exists_nicolasRightmostRayLargeGeometry hZero hHalf hOne hEps
  exact nicolasJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    hRPos hd hGeometry

theorem eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Filter.Eventually (fun z : Complex =>
      IntegrableOn (fun u : Real =>
        nicolasJMellinShiftIntegrandFilled z u) (Ioc (0 : Real) 1))
      (nhds ((1 - rho) - (eps : Complex))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  choose R hRPos hGood using
    exists_nicolasRightmostRayCompactTubeRadius
      hZero hHalf hOne hRay hEps
  have hBall : Membership.mem (nhds center)
      (Metric.ball center (R / 2)) :=
    Metric.ball_mem_nhds _ (by linarith)
  filter_upwards [hBall] with z hz
  have hzClosed : Membership.mem
      (Metric.closedBall center (R / 2)) z :=
    Metric.ball_subset_closedBall hz
  have hzBall : Membership.mem (Metric.ball center R) z := by
    rw [Metric.mem_closedBall] at hzClosed
    rw [Metric.mem_ball]
    linarith
  have hzGood := hGood z (by simpa [center] using hzBall)
  have hContinuous : ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
    intro u hu
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      hu.1 hzGood.1 (hzGood.2 u hu).1 (hzGood.2 u hu).2
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        nicolasJMellinShiftIntegrandFilled z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hInt : IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact hContinuous
  exact hInt.mono_set Ioc_subset_Icc_self

theorem eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_large_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {eps : Real} (hEps : 0 < eps) :
    Filter.Eventually (fun z : Complex =>
      IntegrableOn (fun u : Real =>
        nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)))
      (nhds ((1 - rho) - (eps : Complex))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  choose d R hd hRPos hGeometry using
    exists_nicolasRightmostRayLargeGeometry hZero hHalf hOne hEps
  have hBall : Membership.mem (nhds center) (Metric.ball center R) :=
    Metric.ball_mem_nhds _ hRPos
  filter_upwards [hBall] with z hz
  have hzGeometry := hGeometry z (by simpa [center] using hz)
  exact nicolasJMellinShiftIntegrandFilled_integrableOn_large_of_geometry
    hd hzGeometry.1 hzGeometry.2

theorem eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Filter.EventuallyEq (nhds ((1 - rho) - (eps : Complex)))
      nicolasJShiftedComplexContinuationFilled
      (fun z : Complex =>
        nicolasJShiftedComplexContinuationFilledCompact z +
          nicolasJShiftedComplexContinuationFilledLarge z) := by
  have hCompact :=
    eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
      hZero hHalf hOne hRay hEps
  have hLarge :=
    eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_large_rightmostRay
      hZero hHalf hOne hEps
  filter_upwards [hCompact, hLarge] with z hCompactInt hLargeInt
  unfold nicolasJShiftedComplexContinuationFilled
    nicolasJShiftedComplexContinuationFilledCompact
    nicolasJShiftedComplexContinuationFilledLarge
  rw [<- Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) <= 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hCompactInt
  . exact hLargeInt

theorem nicolasJShiftedComplexContinuationFilled_analyticAt_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilled
      ((1 - rho) - (eps : Complex)) := by
  have hCompact :=
    nicolasJShiftedComplexContinuationFilledCompact_analyticAt_rightmostRay
      hZero hHalf hOne hRay hEps
  have hLarge :=
    nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRay
      hZero hHalf hOne hEps
  have hSum : AnalyticAt Complex (fun z : Complex =>
      nicolasJShiftedComplexContinuationFilledCompact z +
        nicolasJShiftedComplexContinuationFilledLarge z)
      ((1 - rho) - (eps : Complex)) := hCompact.add hLarge
  have hEq :=
    eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large_rightmostRay
      hZero hHalf hOne hRay hEps
  exact (analyticAt_congr hEq).mpr hSum

end

end Robin1984

