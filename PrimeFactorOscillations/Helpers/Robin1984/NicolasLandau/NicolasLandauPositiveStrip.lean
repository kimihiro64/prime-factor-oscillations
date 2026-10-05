/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauPositiveStrip.lean
Original source lines 441-922. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPositiveStripKernel

/-!
# Positive-strip continuation and the Landau convergence conclusion

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

theorem deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compactTube
    {sigma R : Real} (hSigma : sigma < 1 / 2) (hRPos : 0 < R)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball (sigma : Complex) R) z ->
        And (Not (z = 0))
          (And (dist z (sigma : Complex) < 1 / 4)
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0))))
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (sigma : Complex) (R / 4)) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
      z (z + nicolasCompactStripDerivativeStep R n)
  have hzDist : dist z (sigma : Complex) < R / 4 := by
    simpa [Metric.mem_ball] using hz
  have hzClosed : Membership.mem
      (Metric.closedBall (sigma : Complex) (R / 2)) z := by
    rw [Metric.mem_closedBall]
    linarith
  have hShiftClosed : forall n : Nat, Membership.mem
      (Metric.closedBall (sigma : Complex) (R / 2))
      (z + nicolasCompactStripDerivativeStep R n) := by
    intro n
    rw [Metric.mem_closedBall]
    calc
      dist (z + nicolasCompactStripDerivativeStep R n) (sigma : Complex) <=
          dist (z + nicolasCompactStripDerivativeStep R n) z +
            dist z (sigma : Complex) :=
        dist_triangle _ z _
      _ = norm (nicolasCompactStripDerivativeStep R n) +
            dist z (sigma : Complex) := by
        rw [dist_eq_norm]
        simp
      _ <= R / 8 + R / 4 :=
        (add_lt_add_of_le_of_lt
          (norm_nicolasCompactStripDerivativeStep_le hRPos n) hzDist).le
      _ <= R / 2 := by linarith
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    intro n
    have hShift :=
      (nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
        hSigma hRPos hGood (hShiftClosed n)).mono Ioc_subset_Icc_self
    have hBase :=
      (nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
        hSigma hRPos hGood hzClosed).mono Ioc_subset_Icc_self
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
    have hDiffAt : DifferentiableAt Complex
        (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u) z :=
      (nicolasJMellinShiftIntegrandFilled_analyticAt_of_compactTube
        hSigma hRPos hGood huIcc hzClosed).differentiableAt
    have hSlope := hDiffAt.hasDerivAt.tendsto_slope_zero.comp hStepWithin
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
  exact
    (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem norm_deriv_nicolasJMellinShiftIntegrandFilled_le_compactTube
    {sigma R M : Real} (hSigma : sigma < 1 / 2) (hRPos : 0 < R)
    (hMNonneg : 0 <= M)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball (sigma : Complex) R) z ->
        And (Not (z = 0))
          (And (dist z (sigma : Complex) < 1 / 4)
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0))))
    (hKernelBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem
            (Metric.closedBall (sigma : Complex) (R / 2)) z ->
            norm (nicolasJMellinShiftIntegrandFilled z u) <= M)
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (sigma : Complex) (R / 4)) z) :
    norm (deriv (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z) <= 8 * M / R := by
  let f : Complex -> Complex := fun w =>
    nicolasJMellinShiftIntegrandFilled w u
  let r : Real := R / 4
  have hzDist : dist z (sigma : Complex) < R / 4 := by
    simpa [Metric.mem_ball] using hz
  have hSmallSubset : Metric.ball z r <=
      Metric.closedBall (sigma : Complex) (R / 2) := by
    intro w hw
    rw [Metric.mem_ball] at hw
    rw [Metric.mem_closedBall]
    calc
      dist w (sigma : Complex) <= dist w z + dist z (sigma : Complex) :=
        dist_triangle _ z _
      _ <= R / 4 + R / 4 := by
        dsimp [r] at hw
        exact (add_lt_add hw hzDist).le
      _ <= R / 2 := by linarith
  have hzClosed : Membership.mem
      (Metric.closedBall (sigma : Complex) (R / 2)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self (by dsimp [r]; linarith)
  have hDiff : DifferentiableOn Complex f (Metric.ball z r) := by
    intro w hw
    exact
      (nicolasJMellinShiftIntegrandFilled_analyticAt_of_compactTube
        hSigma hRPos hGood hu (hSmallSubset hw)).differentiableAt.differentiableWithinAt
  have hMaps : MapsTo f (Metric.ball z r)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwBound : norm (f w) <= M := by
      dsimp [f]
      exact hKernelBound u hu w (hSmallSubset hw)
    have hzBound : norm (f z) <= M := by
      dsimp [f]
      exact hKernelBound u hu z hzClosed
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

theorem nicolasJShiftedComplexContinuationFilledCompact_analyticAt_pos_real
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledCompact
      (sigma : Complex) := by
  choose R M hRPos hMNonneg hGood hKernelBound using
    exists_nicolasPositiveCompactKernelBound hSigmaPos hSigma
  let s : Set Complex := Metric.ball (sigma : Complex) (R / 4)
  have hHasDeriv : forall z : Complex, Membership.mem s z ->
      HasDerivAt nicolasJShiftedComplexContinuationFilledCompact
        (integral (volume.restrict (Ioc (0 : Real) 1)) (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)) z := by
    intro z hz
    let F : Complex -> Real -> Complex := fun w => fun u =>
      nicolasJMellinShiftIntegrandFilled w u
    let F' : Complex -> Real -> Complex := fun w => fun u =>
      deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
    have hsNhd : Membership.mem (nhds z) s := by
      dsimp [s] at hz
      exact Metric.isOpen_ball.mem_nhds hz
    have hFMeas : Filter.Eventually
        (fun w : Complex => AEStronglyMeasurable (F w)
          (volume.restrict (Ioc (0 : Real) 1))) (nhds z) := by
      filter_upwards [hsNhd] with w hw
      have hwDist : dist w (sigma : Complex) < R / 4 := by
        simpa [s, Metric.mem_ball] using hw
      have hwClosed : Membership.mem
          (Metric.closedBall (sigma : Complex) (R / 2)) w := by
        rw [Metric.mem_closedBall]
        linarith
      have hCont :=
        (nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
          hSigma hRPos hGood hwClosed).mono Ioc_subset_Icc_self
      dsimp [F]
      exact hCont.aestronglyMeasurable measurableSet_Ioc
    have hzDist : dist z (sigma : Complex) < R / 4 := by
      simpa [s, Metric.mem_ball] using hz
    have hzClosed : Membership.mem
        (Metric.closedBall (sigma : Complex) (R / 2)) z := by
      rw [Metric.mem_closedBall]
      linarith
    have hFInt : Integrable (F z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      have hCont :=
        nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
          hSigma hRPos hGood hzClosed
      have hInt : IntegrableOn (fun u : Real =>
          nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) :=
        by
          apply ContinuousOn.integrableOn_compact isCompact_Icc
          exact hCont
      exact (hInt.mono_set Ioc_subset_Icc_self)
    have hF'Meas : AEStronglyMeasurable (F' z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      dsimp [F']
      exact
        deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compactTube
          hSigma hRPos hGood (by simpa [s] using hz)
    have hBound : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          norm (F' w u) <= 8 * M / R)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      have huIcc : Membership.mem (Icc (0 : Real) 1) u :=
        Ioc_subset_Icc_self hu
      dsimp [F']
      exact norm_deriv_nicolasJMellinShiftIntegrandFilled_le_compactTube
        hSigma hRPos hMNonneg hGood hKernelBound huIcc
          (by simpa [s] using hw)
    have hBoundInt : IntegrableOn (fun _ : Real => 8 * M / R)
        (Ioc (0 : Real) 1) := by
      have hInt : IntegrableOn (fun _ : Real => 8 * M / R)
          (Icc (0 : Real) 1) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact continuousOn_const
      exact hInt.mono_set Ioc_subset_Icc_self
    have hDiff : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          HasDerivAt (fun v : Complex => F v u) (F' w u) w)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      have huIcc : Membership.mem (Icc (0 : Real) 1) u :=
        Ioc_subset_Icc_self hu
      have hwDist : dist w (sigma : Complex) < R / 4 := by
        simpa [s, Metric.mem_ball] using hw
      have hwClosed : Membership.mem
          (Metric.closedBall (sigma : Complex) (R / 2)) w := by
        rw [Metric.mem_closedBall]
        linarith
      have hAt :=
        nicolasJMellinShiftIntegrandFilled_analyticAt_of_compactTube
          hSigma hRPos hGood huIcc hwClosed
      dsimp [F, F']
      exact hAt.differentiableAt.hasDerivAt
    have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := fun _ : Real => 8 * M / R)
      hsNhd hFMeas hFInt hF'Meas hBound hBoundInt hDiff
    unfold nicolasJShiftedComplexContinuationFilledCompact
    simpa [F, F'] using hMain.2
  have hDiffOn : DifferentiableOn Complex
      nicolasJShiftedComplexContinuationFilledCompact s := by
    intro z hz
    exact (hHasDeriv z hz).differentiableAt.differentiableWithinAt
  apply hDiffOn.analyticAt
  dsimp [s]
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith : 0 < R / 4))

theorem eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_pos_real
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    Filter.Eventually (fun z : Complex =>
      IntegrableOn (fun u : Real =>
        nicolasJMellinShiftIntegrandFilled z u) (Ioc (0 : Real) 1))
      (nhds (sigma : Complex)) := by
  choose R hRPos hGood using
    exists_nicolasPositiveCompactTubeRadius hSigmaPos hSigma
  have hBall : Membership.mem (nhds (sigma : Complex))
      (Metric.ball (sigma : Complex) (R / 2)) :=
    Metric.ball_mem_nhds _ (by linarith)
  filter_upwards [hBall] with z hz
  have hzClosed : Membership.mem
      (Metric.closedBall (sigma : Complex) (R / 2)) z :=
    Metric.ball_subset_closedBall hz
  have hCont :=
    nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
      hSigma hRPos hGood hzClosed
  have hInt : IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact hCont
  exact hInt.mono_set Ioc_subset_Icc_self

theorem eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    Filter.EventuallyEq (nhds (sigma : Complex))
      nicolasJShiftedComplexContinuationFilled
      (fun z : Complex =>
        nicolasJShiftedComplexContinuationFilledCompact z +
          nicolasJShiftedComplexContinuationFilledLarge z) := by
  have hCompact :=
    eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_pos_real
      hSigmaPos hSigma
  have hSigmaHalf : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) (sigma : Complex) := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hSigmaPos]
    exact hSigma
  have hHalf : Membership.mem (nhds (sigma : Complex))
      (Metric.ball (0 : Complex) (1 / 2 : Real)) :=
    Metric.isOpen_ball.mem_nhds hSigmaHalf
  filter_upwards [hCompact, hHalf] with z hCompactInt hzHalf
  have hLargeInt :=
    nicolasJMellinShiftIntegrandFilled_integrableOn_large_half hzHalf
  unfold nicolasJShiftedComplexContinuationFilled
    nicolasJShiftedComplexContinuationFilledCompact
    nicolasJShiftedComplexContinuationFilledLarge
  rw [<- Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) <= 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hCompactInt
  . exact hLargeInt

theorem nicolasJShiftedComplexContinuationFilled_analyticAt_pos_real
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilled
      (sigma : Complex) := by
  have hCompact :=
    nicolasJShiftedComplexContinuationFilledCompact_analyticAt_pos_real
      hSigmaPos hSigma
  have hLarge :=
    nicolasJShiftedComplexContinuationFilledLarge_analyticAt_pos_real
      hSigmaPos hSigma
  have hSum : AnalyticAt Complex (fun z : Complex =>
      nicolasJShiftedComplexContinuationFilledCompact z +
        nicolasJShiftedComplexContinuationFilledLarge z) (sigma : Complex) :=
    hCompact.add hLarge
  have hEq :=
    eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large
      hSigmaPos hSigma
  exact (analyticAt_congr hEq).mpr hSum

theorem nicolasJShiftedRealContinuationFilled_analyticAt_pos
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    AnalyticAt Real nicolasJShiftedRealContinuationFilled sigma := by
  unfold nicolasJShiftedRealContinuationFilled
  exact realAnalyticAt_re_comp_of_complexAnalyticAt
    (nicolasJShiftedComplexContinuationFilled_analyticAt_pos_real
      hSigmaPos hSigma)

theorem nicolasLandauPositiveMellinContinuationFilled_analyticAt_pos
    {X b sigma : Real} (hX : 3 <= X) (hSigmaPos : 0 < sigma)
    (hSigmaHalf : sigma < 1 / 2) (hSigmaB : sigma < b) :
    AnalyticAt Real (nicolasLandauPositiveMellinContinuationFilled X b)
      sigma := by
  have hShift : AnalyticAt Real nicolasJShiftedRealContinuationFilled sigma :=
    nicolasJShiftedRealContinuationFilled_analyticAt_pos
      hSigmaPos hSigmaHalf
  have hStartup : AnalyticAt Real
      (fun a : Real =>
        Complex.re (nicolasJComplexMellinStartup X (a : Complex))) sigma :=
    realAnalyticAt_re_comp_of_complexAnalyticAt
      (nicolasJComplexMellinStartup_analyticAt hX (sigma : Complex))
  have hRpow : AnalyticAt Real
      (nicolasLandauRpowMellinContinuation X b) sigma :=
    nicolasLandauRpowMellinContinuation_analyticAt
      (lt_of_lt_of_le (by norm_num) hX) hSigmaB
  unfold nicolasLandauPositiveMellinContinuationFilled
  exact (hShift.sub hStartup).add hRpow

theorem nicolasLandauPositiveMellinContinuationFilled_analyticAt_neg
    {X b sigma : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    (hSigma : sigma < 0) :
    AnalyticAt Real (nicolasLandauPositiveMellinContinuationFilled X b)
      sigma := by
  have hBelow : forall a : Real, a < 0 ->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * nicolasLandauPositiveTail b x) (Ioi X) := by
    intro a ha
    exact nicolasLandauPositiveTail_integrableOn_of_neg hX hb ha
  have hInterior : Membership.mem
      (interior (integrableExpSet (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b))) sigma :=
    interior_integrableExpSet_log_nicolasLandau_of_below
      hX hPos hBelow sigma hSigma
  have hMgf : AnalyticAt Real
      (mgf (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b)) sigma :=
    analyticAt_mgf hInterior
  have hEq : Filter.EventuallyEq (nhds sigma)
      (mgf (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b))
      (nicolasLandauPositiveMellinContinuationFilled X b) := by
    filter_upwards [Iio_mem_nhds hSigma] with a ha
    rw [mgf_log_nicolasLandauPositiveMeasure_eq_mellin hX hPos]
    calc
      nicolasLandauPositiveMellin X b a =
          nicolasLandauPositiveMellinContinuation X b a :=
        nicolasLandauPositiveMellin_eq_continuation_of_neg hX hb ha
      _ = nicolasLandauPositiveMellinContinuationFilled X b a :=
        (nicolasLandauPositiveMellinContinuationFilled_eq_raw_of_neg
          hX ha).symm
  exact (analyticAt_congr hEq).mp hMgf

theorem nicolasLandauPositiveMellinContinuationFilled_analyticAt_lt
    {X b sigma : Real} (hX : 3 <= X) (hb : 0 < b)
    (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    (hSigma : sigma < b) :
    AnalyticAt Real (nicolasLandauPositiveMellinContinuationFilled X b)
      sigma := by
  rcases lt_trichotomy sigma 0 with hSigmaNeg | hSigmaZero | hSigmaPos
  . exact nicolasLandauPositiveMellinContinuationFilled_analyticAt_neg
      hX hb hPos hSigmaNeg
  . subst sigma
    exact nicolasLandauPositiveMellinContinuationFilled_analyticAt_zero hX hb
  . exact nicolasLandauPositiveMellinContinuationFilled_analyticAt_pos
      hX hSigmaPos (lt_of_lt_of_le hSigma hbHalf) hSigma

theorem Iio_subset_interior_integrableExpSet_nicolasLandau_of_positive
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x) :
    Iio b <= interior
      (integrableExpSet (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b)) := by
  have hBelow : forall a : Real, a < 0 ->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * nicolasLandauPositiveTail b x) (Ioi X) := by
    intro a ha
    exact nicolasLandauPositiveTail_integrableOn_of_neg hX hb ha
  have hNeg : forall a : Real, a < 0 -> Membership.mem
      (interior (integrableExpSet (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b))) a :=
    interior_integrableExpSet_log_nicolasLandau_of_below
      hX hPos hBelow
  have hAnalytic : forall sigma : Real, sigma < b ->
      AnalyticAt Real (nicolasLandauPositiveMellinContinuationFilled X b)
        sigma := by
    intro sigma hSigma
    exact nicolasLandauPositiveMellinContinuationFilled_analyticAt_lt
      hX hb hbHalf hPos hSigma
  have hEqNeg : forall a : Real, a < 0 ->
      mgf (fun x : Real => Real.log x)
          (nicolasLandauPositiveMeasure X b) a =
        nicolasLandauPositiveMellinContinuationFilled X b a := by
    intro a ha
    rw [mgf_log_nicolasLandauPositiveMeasure_eq_mellin hX hPos]
    calc
      nicolasLandauPositiveMellin X b a =
          nicolasLandauPositiveMellinContinuation X b a :=
        nicolasLandauPositiveMellin_eq_continuation_of_neg hX hb ha
      _ = nicolasLandauPositiveMellinContinuationFilled X b a :=
        (nicolasLandauPositiveMellinContinuationFilled_eq_raw_of_neg
          hX ha).symm
  exact Iio_subset_interior_integrableExpSet_of_analyticContinuation
    (ae_log_nonneg_nicolasLandauPositiveMeasure hX) hNeg hAnalytic hEqNeg

end

end Robin1984

