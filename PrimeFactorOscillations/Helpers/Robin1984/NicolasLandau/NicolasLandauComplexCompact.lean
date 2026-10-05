/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauComplexFrontier.lean
Original source lines 186-606. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauComplexFrontierBase

/-!
# Compact continuation along the zero-free horizontal ray

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem nicolasJShiftedComplexContinuationFilledCompact_analyticAt_of_tube
    {center : Complex} {R : Real} (hRPos : 0 < R)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (Not (z = 0))
          (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
            And (Not ((((u + 1 : Real) : Complex) - z) = 0))
              (Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0)))) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledCompact
      center := by
  let K : Set (Prod Real Complex) := fun p =>
    And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem (Metric.closedBall center (R / 2)) p.2)
  let F : Prod Real Complex -> Complex := fun p =>
    nicolasJMellinShiftIntegrandFilled p.2 p.1
  have hKCompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_Icc : IsCompact (Icc (0 : Real) 1)).prod
      (isCompact_closedBall center (R / 2))
  have hKNonempty : K.Nonempty := by
    refine Exists.intro ((0 : Real), center) ?_
    dsimp [K]
    exact And.intro (And.intro le_rfl zero_le_one)
      (Metric.mem_closedBall_self (by linarith))
  have hContinuous : ContinuousOn F K := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    change And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem (Metric.closedBall center (R / 2)) p.2) at hp
    have hpBall : Membership.mem (Metric.ball center R) p.2 := by
      rw [Metric.mem_closedBall] at hp
      rw [Metric.mem_ball]
      linarith
    have hpGood := hGood p.2 hpBall
    exact nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      hp.1.1 hpGood.1 (hpGood.2 p.1 hp.1).1 (hpGood.2 p.1 hp.1).2
  choose p hpK hpMax using hKCompact.exists_isMaxOn hKNonempty hContinuous.norm
  let M : Real := norm (F p)
  have hMNonneg : 0 <= M := norm_nonneg _
  have hKernelBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.closedBall center (R / 2)) z ->
            norm (nicolasJMellinShiftIntegrandFilled z u) <= M := by
    intro u hu z hz
    have hPair : K (u, z) := by
      dsimp [K]
      exact And.intro hu hz
    simpa [M, F] using hpMax hPair
  have hContinuousU : forall z : Complex,
      Membership.mem (Metric.closedBall center (R / 2)) z ->
        ContinuousOn (fun u : Real =>
          nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
    intro z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGood := hGood z hzBall
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
  have hAnalytic : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.closedBall center (R / 2)) z ->
            AnalyticAt Complex (fun w : Complex =>
              nicolasJMellinShiftIntegrandFilled w u) z := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGood := hGood z hzBall
    exact
      nicolasJMellinShiftIntegrandFilled_analyticAt_of_ne_zero_of_factor_ne_zero
        hu.1 hzGood.1 (hzGood.2 u hu).1 (hzGood.2 u hu).2
  have hDerivativeMeasurable : forall z : Complex,
      Membership.mem (Metric.ball center (R / 4)) z ->
        AEStronglyMeasurable (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)
          (volume.restrict (Ioc (0 : Real) 1)) := by
    intro z hz
    let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
      slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
        z (z + nicolasCompactStripDerivativeStep R n)
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      linarith
    have hShiftClosed : forall n : Nat,
        Membership.mem (Metric.closedBall center (R / 2))
          (z + nicolasCompactStripDerivativeStep R n) := by
      intro n
      rw [Metric.mem_closedBall]
      calc
        dist (z + nicolasCompactStripDerivativeStep R n) center <=
            dist (z + nicolasCompactStripDerivativeStep R n) z +
              dist z center := dist_triangle _ z _
        _ = norm (nicolasCompactStripDerivativeStep R n) +
              dist z center := by rw [dist_eq_norm]; simp
        _ <= R / 8 + R / 4 :=
          (add_lt_add_of_le_of_lt
            (norm_nicolasCompactStripDerivativeStep_le hRPos n) hzDist).le
        _ <= R / 2 := by linarith
    have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      intro n
      have hShift := (hContinuousU _ (hShiftClosed n)).mono
        Ioc_subset_Icc_self
      have hBase := (hContinuousU z hzClosed).mono Ioc_subset_Icc_self
      have hShiftMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled
            (z + nicolasCompactStripDerivativeStep R n) u)
          (volume.restrict (Ioc (0 : Real) 1)) :=
        hShift.aestronglyMeasurable measurableSet_Ioc
      have hBaseMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled z u)
          (volume.restrict (Ioc (0 : Real) 1)) :=
        hBase.aestronglyMeasurable measurableSet_Ioc
      have hEq : slopeSeq n = fun u : Real =>
          Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z) *
            (nicolasJMellinShiftIntegrandFilled
                (z + nicolasCompactStripDerivativeStep R n) u -
              nicolasJMellinShiftIntegrandFilled z u) := by
        funext u
        dsimp [slopeSeq]
        unfold slope
        simp only [smul_eq_mul, vsub_eq_sub]
      rw [hEq]
      exact ((hShiftMeas.sub hBaseMeas).const_mul
        (Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z))).aemeasurable
    have hStepWithin : Tendsto (nicolasCompactStripDerivativeStep R) atTop
        (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact And.intro (nicolasCompactStripDerivativeStep_tendsto_zero R)
        (Eventually.of_forall (fun n : Nat =>
          Set.mem_compl_singleton_iff.mpr
            (nicolasCompactStripDerivativeStep_ne_zero hRPos n)))
    have hTendsto : Filter.Eventually
        (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
          (nhds (deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)))
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have huIcc : Membership.mem (Icc (0 : Real) 1) u :=
        Ioc_subset_Icc_self hu
      have hSlope := (hAnalytic u huIcc z hzClosed).differentiableAt.hasDerivAt
        |>.tendsto_slope_zero.comp hStepWithin
      change Tendsto (fun n : Nat =>
        Inv.inv (nicolasCompactStripDerivativeStep R n) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasCompactStripDerivativeStep R n) u -
            nicolasJMellinShiftIntegrandFilled z u))
        atTop (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
      exact hSlope
    exact (aemeasurable_of_tendsto_metrizable_ae'
      hMeas hTendsto).aestronglyMeasurable
  have hDerivativeBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.ball center (R / 4)) z ->
            norm (deriv (fun w : Complex =>
              nicolasJMellinShiftIntegrandFilled w u) z) <= 8 * M / R := by
    intro u hu z hz
    let f : Complex -> Complex := fun w =>
      nicolasJMellinShiftIntegrandFilled w u
    let r : Real := R / 4
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hSmallSubset : Metric.ball z r <=
        Metric.closedBall center (R / 2) := by
      intro w hw
      rw [Metric.mem_ball] at hw
      rw [Metric.mem_closedBall]
      calc
        dist w center <= dist w z + dist z center := dist_triangle _ z _
        _ <= R / 4 + R / 4 := by
          dsimp [r] at hw
          exact (add_lt_add hw hzDist).le
        _ <= R / 2 := by linarith
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      apply hSmallSubset
      exact Metric.mem_ball_self (by dsimp [r]; linarith)
    have hDiff : DifferentiableOn Complex f (Metric.ball z r) := by
      intro w hw
      exact (hAnalytic u hu w (hSmallSubset hw)).differentiableAt.differentiableWithinAt
    have hMaps : MapsTo f (Metric.ball z r)
        (Metric.closedBall (f z) (2 * M)) := by
      intro w hw
      have hwBound : norm (f w) <= M := hKernelBound u hu w (hSmallSubset hw)
      have hzBound : norm (f z) <= M := hKernelBound u hu z hzClosed
      rw [Metric.mem_closedBall]
      calc
        dist (f w) (f z) <= norm (f w) + norm (f z) := by
          simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
        _ <= M + M := add_le_add hwBound hzBound
        _ = 2 * M := by ring
    have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
      hDiff hMaps (by dsimp [r]; linarith)
    change norm (deriv f z) <= 8 * M / R
    calc
      norm (deriv f z) <= (2 * M) / r := hCauchy
      _ = 8 * M / R := by
        dsimp [r]
        field_simp [hRPos.ne']
        ring
  let s : Set Complex := Metric.ball center (R / 4)
  have hHasDeriv : forall z : Complex, Membership.mem s z ->
      HasDerivAt nicolasJShiftedComplexContinuationFilledCompact
        (integral (volume.restrict (Ioc (0 : Real) 1)) (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)) z := by
    intro z hz
    let G : Complex -> Real -> Complex := fun w => fun u =>
      nicolasJMellinShiftIntegrandFilled w u
    let G' : Complex -> Real -> Complex := fun w => fun u =>
      deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
    have hsNhd : Membership.mem (nhds z) s :=
      Metric.isOpen_ball.mem_nhds hz
    have hGMeas : Filter.Eventually
        (fun w : Complex => AEStronglyMeasurable (G w)
          (volume.restrict (Ioc (0 : Real) 1))) (nhds z) := by
      filter_upwards [hsNhd] with w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [G]
      exact ((hContinuousU w hwClosed).mono Ioc_subset_Icc_self)
        |>.aestronglyMeasurable measurableSet_Ioc
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      have hzDist : dist z center < R / 4 := by
        simpa [s, Metric.mem_ball] using hz
      linarith
    have hGInt : Integrable (G z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      have hInt : IntegrableOn (fun u : Real =>
          nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact hContinuousU z hzClosed
      exact hInt.mono_set Ioc_subset_Icc_self
    have hG'Meas : AEStronglyMeasurable (G' z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      dsimp [G']
      exact hDerivativeMeasurable z hz
    have hBound : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          norm (G' w u) <= 8 * M / R)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      exact hDerivativeBound u (Ioc_subset_Icc_self hu) w hw
    have hBoundInt : IntegrableOn (fun _ : Real => 8 * M / R)
        (Ioc (0 : Real) 1) := by
      have hInt : IntegrableOn (fun _ : Real => 8 * M / R)
          (Icc (0 : Real) 1) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact continuousOn_const
      exact hInt.mono_set Ioc_subset_Icc_self
    have hDiff : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          HasDerivAt (fun v : Complex => G v u) (G' w u) w)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [G, G']
      exact (hAnalytic u (Ioc_subset_Icc_self hu) w hwClosed)
        |>.differentiableAt.hasDerivAt
    have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := G) (F' := G') (bound := fun _ : Real => 8 * M / R)
      hsNhd hGMeas hGInt hG'Meas hBound hBoundInt hDiff
    unfold nicolasJShiftedComplexContinuationFilledCompact
    simpa [G, G'] using hMain.2
  have hDiffOn : DifferentiableOn Complex
      nicolasJShiftedComplexContinuationFilledCompact s := by
    intro z hz
    exact (hHasDeriv z hz).differentiableAt.differentiableWithinAt
  apply hDiffOn.analyticAt
  dsimp [s]
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith : 0 < R / 4))

theorem exists_nicolasRightmostRayCompactTubeRadius
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Exists fun R : Real => And (0 < R)
      (forall z : Complex,
        Membership.mem
          (Metric.ball ((1 - rho) - (eps : Complex)) R) z ->
          And (Not (z = 0))
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              And (Not ((((u + 1 : Real) : Complex) - z) = 0))
                (Not (nicolasZetaPoleFactor
                  (((u + 1 : Real) : Complex) - z) = 0)))) := by
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
  have hZeroNhd : Filter.Eventually (fun z : Complex => Not (z = 0))
      (nhds center) := continuousAt_id.eventually_ne hCenterNe
  have hShiftNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not ((((u + 1 : Real) : Complex) - z) = 0))
      (nhds center) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    have hShiftIm :
        ((((u + 1 : Real) : Complex) - center)).im = rho.im := by
      rw [Complex.sub_im, Complex.ofReal_im, hCenterIm]
      ring
    have hShiftNe : Not ((((u + 1 : Real) : Complex) - center) = 0) := by
      intro hEq
      have hZeroIm : ((((u + 1 : Real) : Complex) - center)).im = 0 := by
        rw [hEq]
        simp
      exact hIm (hShiftIm.symm.trans hZeroIm)
    let G : Prod Complex Real -> Complex := fun p =>
      ((p.2 + 1 : Real) : Complex) - p.1
    have hContinuous : Continuous G := by
      dsimp [G]
      fun_prop
    have hAt : Not (G (center, u) = 0) := by
      simpa [G] using hShiftNe
    exact hContinuous.continuousAt.eventually_ne hAt
  have hFactorNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not (nicolasZetaPoleFactor
          (((u + 1 : Real) : Complex) - z) = 0))
      (nhds center) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    let s : Complex := rho + ((eps + u : Real) : Complex)
    have hShift : (((u + 1 : Real) : Complex) - center) = s := by
      dsimp [center, s]
      push_cast
      ring
    have hZeta : Not (riemannZeta s = 0) := by
      dsimp [s]
      exact hRay (eps + u) (by linarith [hu.1])
    have hFactor : Not (nicolasZetaPoleFactor s = 0) := by
      by_cases hsOne : s = 1
      . rw [hsOne, nicolasZetaPoleFactor_one]
        norm_num
      . intro hFactorZero
        have hIdentity := riemannZeta_eq_nicolasZetaPoleFactor_div hsOne
        rw [hFactorZero, zero_div] at hIdentity
        exact hZeta hIdentity
    let G : Prod Complex Real -> Complex := fun p =>
      nicolasZetaPoleFactor (((p.2 + 1 : Real) : Complex) - p.1)
    have hAffine : Continuous (fun p : Prod Complex Real =>
        (((p.2 + 1 : Real) : Complex) - p.1)) := by
      fun_prop
    have hContinuous : Continuous G := by
      dsimp [G]
      exact nicolasZetaPoleFactor_differentiable.continuous.comp hAffine
    have hAt : Not (nicolasZetaPoleFactor
        (((u + 1 : Real) : Complex) - center) = 0) := by
      rw [hShift]
      exact hFactor
    have hPairAt : Not (G (center, u) = 0) := by
      simpa [G] using hAt
    exact hContinuous.continuousAt.eventually_ne hPairAt
  have hAll := hZeroNhd.and (hShiftNhd.and hFactorNhd)
  choose R hRPos hR using Metric.mem_nhds_iff.1 hAll
  refine Exists.intro R (And.intro hRPos ?_)
  intro z hz
  have hzGood := hR hz
  exact And.intro hzGood.1 (fun u hu =>
    And.intro (hzGood.2.1 u hu) (hzGood.2.2 u hu))

theorem nicolasJShiftedComplexContinuationFilledCompact_analyticAt_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledCompact
      ((1 - rho) - (eps : Complex)) := by
  choose R hRPos hGood using
    exists_nicolasRightmostRayCompactTubeRadius
      hZero hHalf hOne hRay hEps
  exact nicolasJShiftedComplexContinuationFilledCompact_analyticAt_of_tube
    hRPos hGood

end

end Robin1984

