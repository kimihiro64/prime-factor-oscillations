/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauComplexFrontier.lean
Original source lines 607-1071. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauComplexCompact

/-!
# The large-parameter continuation away from the origin

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem norm_nicolasJShiftNumeratorFilled_le_of_re_le_threeQuarter
    {u : Real} (hu : 1 < u) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) :
    norm (nicolasJShiftNumeratorFilled u z) <=
      5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 < s0.re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hDen1 : (1 / 4 : Real) < s1.re - 1 := by
    dsimp [s1, s0]
    linarith
  have hShiftRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs1
  have hShiftNumerator : (3 : Real) ^ (1 - s1.re) <=
      (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [s1, s0]
    linarith
  have hShiftPowerNonneg : 0 <= (3 : Real) ^ (1 - s1.re) :=
    Real.rpow_nonneg (by norm_num) _
  have hShiftFraction : (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
      4 * (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
          (3 : Real) ^ (1 - s1.re) / (1 / 4 : Real) :=
        div_le_div_of_nonneg_left hShiftPowerNonneg (by norm_num) hDen1.le
      _ = 4 * (3 : Real) ^ (1 - s1.re) := by ring
      _ <= 4 * (3 : Real) ^ (-u + (3 / 4 : Real)) :=
        mul_le_mul_of_nonneg_left hShiftNumerator (by norm_num)
  have hShift : norm (nicolasPsiMellinTailContinuationFilled s1) <=
      4 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      norm (nicolasPsiMellinTailContinuationFilled s1) <=
          (Real.log 4 + 5) *
            ((3 : Real) ^ (1 - s1.re) / (s1.re - 1)) := hShiftRaw
      _ <= (Real.log 4 + 5) *
          (4 * (3 : Real) ^ (-u + (3 / 4 : Real))) :=
        mul_le_mul_of_nonneg_left hShiftFraction (by positivity)
      _ = 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring
  have hBaseRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs0
  have hBase : norm (nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) * (3 : Real) ^ (-u) := by
    have hPowNonneg : 0 <= (3 : Real) ^ (-u) :=
      Real.rpow_nonneg (by norm_num) _
    have hS0Exponent : 1 - s0.re = -u := by
      dsimp [s0]
      ring
    have hS0Denominator : s0.re - 1 = u := by
      dsimp [s0]
      ring
    rw [hS0Exponent, hS0Denominator] at hBaseRaw
    calc
      norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (Real.log 4 + 5) * ((3 : Real) ^ (-u) / u) := hBaseRaw
      _ <= (Real.log 4 + 5) * ((3 : Real) ^ (-u) / 1) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hPowNonneg zero_lt_one hu.le)
          (by positivity)
      _ = (Real.log 4 + 5) * (3 : Real) ^ (-u) := by ring
  have hPowerNorm : norm ((3 : Complex) ^ z) =
      (3 : Real) ^ z.re := by
    change norm (((3 : Real) : Complex) ^ z) = (3 : Real) ^ z.re
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hPowerProduct : norm ((3 : Complex) ^ z *
      nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    rw [norm_mul, hPowerNorm]
    calc
      (3 : Real) ^ z.re *
          norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (3 : Real) ^ z.re *
            ((Real.log 4 + 5) * (3 : Real) ^ (-u)) :=
        mul_le_mul_of_nonneg_left hBase
          (Real.rpow_nonneg (by norm_num) _)
      _ = (Real.log 4 + 5) *
          ((3 : Real) ^ z.re * (3 : Real) ^ (-u)) := by ring
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re + (-u)) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 3)]
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re - u) := by
        congr 2
      _ <= (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
  unfold nicolasJShiftNumeratorFilled
  change norm (nicolasPsiMellinTailContinuationFilled s1 -
      (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <= _
  calc
    norm (nicolasPsiMellinTailContinuationFilled s1 -
        (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <=
        norm (nicolasPsiMellinTailContinuationFilled s1) +
          norm ((3 : Complex) ^ z *
            nicolasPsiMellinTailContinuationFilled s0) := norm_sub_le _ _
    _ <= 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) +
        (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) :=
      add_le_add hShift hPowerProduct
    _ = 5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring

def nicolasJLargeMajorantAtDistance (d u : Real) : Real :=
  (5 / d) * (Real.log 4 + 5) * (u + 1) *
    (3 : Real) ^ (-u + (3 / 4 : Real))

theorem nicolasJLargeMajorantAtDistance_integrableOn
    {d : Real} (hd : 0 < d) :
    IntegrableOn (nicolasJLargeMajorantAtDistance d) (Ioi (1 : Real)) := by
  have hScaled := nicolasJLargeMajorantHalf_integrableOn.const_mul
    (3 / (4 * d))
  apply hScaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  unfold nicolasJLargeMajorantAtDistance nicolasJLargeMajorantHalf
  field_simp [hd.ne']
  ring

theorem norm_nicolasJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge
    {d u : Real} (hd : 0 < d) (hu : 1 < u) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) (hzNorm : d <= norm z) :
    norm (nicolasJMellinShiftIntegrandFilled z u) <=
      nicolasJLargeMajorantAtDistance d u := by
  have hzNe : Not (z = 0) := by
    intro hEq
    rw [hEq, norm_zero] at hzNorm
    linarith
  have hNumerator :=
    norm_nicolasJShiftNumeratorFilled_le_of_re_le_threeQuarter hu hzRe
  have hInv : norm (Inv.inv z) <= 1 / d := by
    rw [norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le hd hzNorm
  have huPos : 0 < u + 1 := by linarith
  unfold nicolasJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzNe]
  unfold slope
  rw [nicolasJShiftNumeratorFilled_zero]
  simp only [smul_eq_mul, vsub_eq_sub, sub_zero]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huPos,
    norm_mul]
  calc
    (u + 1) * (norm (Inv.inv z) *
        norm (nicolasJShiftNumeratorFilled u z)) <=
        (u + 1) * ((1 / d) *
          (5 * (Real.log 4 + 5) *
            (3 : Real) ^ (-u + (3 / 4 : Real)))) := by
      apply mul_le_mul_of_nonneg_left _ huPos.le
      exact mul_le_mul hInv hNumerator (norm_nonneg _)
        (by positivity)
    _ = nicolasJLargeMajorantAtDistance d u := by
      unfold nicolasJLargeMajorantAtDistance
      field_simp [hd.ne']

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    {center : Complex} {R d : Real} (hRPos : 0 < R) (hd : 0 < d)
    (hGeometry : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (z.re <= (3 / 4 : Real)) (d <= norm z)) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      center := by
  have hPointData : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          And (Not (z = 0))
            (And (Not ((((u + 1 : Real) : Complex) - z) = 0))
              (Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0))) := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGeometry := hGeometry z hzBall
    have hzNe : Not (z = 0) := by
      intro hEq
      rw [hEq, norm_zero] at hzGeometry
      linarith
    have hsRe : 1 < ((((u + 1 : Real) : Complex) - z).re) := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [hzGeometry.1]
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
    exact And.intro hzNe (And.intro hsZero hFactor)
  have hKernelBound : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          norm (nicolasJMellinShiftIntegrandFilled z u) <=
            nicolasJLargeMajorantAtDistance d u := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGeometry := hGeometry z hzBall
    exact norm_nicolasJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge
      hd hu hzGeometry.1 hzGeometry.2
  have hContinuousU : forall z : Complex,
      Membership.mem (Metric.closedBall center (R / 2)) z ->
        ContinuousOn (fun u : Real =>
          nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
    intro z hz u hu
    have hData := hPointData u (mem_Ioi.mp hu) z hz
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      (by linarith [mem_Ioi.mp hu] : 0 <= u)
      hData.1 hData.2.1 hData.2.2
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        nicolasJMellinShiftIntegrandFilled z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hAnalytic : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          AnalyticAt Complex (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z := by
    intro u hu z hz
    have hData := hPointData u hu z hz
    exact
      nicolasJMellinShiftIntegrandFilled_analyticAt_of_ne_zero_of_factor_ne_zero
        (by linarith [hu] : 0 <= u) hData.1 hData.2.1 hData.2.2
  have hDerivativeMeasurable : forall z : Complex,
      Membership.mem (Metric.ball center (R / 4)) z ->
        AEStronglyMeasurable (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)
          (volume.restrict (Ioi (1 : Real))) := by
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
        (volume.restrict (Ioi (1 : Real))) := by
      intro n
      have hShift := hContinuousU _ (hShiftClosed n)
      have hBase := hContinuousU z hzClosed
      have hShiftMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled
            (z + nicolasCompactStripDerivativeStep R n) u)
          (volume.restrict (Ioi (1 : Real))) :=
        hShift.aestronglyMeasurable measurableSet_Ioi
      have hBaseMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled z u)
          (volume.restrict (Ioi (1 : Real))) :=
        hBase.aestronglyMeasurable measurableSet_Ioi
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
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hSlope := (hAnalytic u hu z hzClosed).differentiableAt.hasDerivAt
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
  have hDerivativeBound : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.ball center (R / 4)) z ->
          norm (deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z) <=
              (8 / R) * nicolasJLargeMajorantAtDistance d u := by
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
        (Metric.closedBall (f z)
          (2 * nicolasJLargeMajorantAtDistance d u)) := by
      intro w hw
      have hwBound := hKernelBound u hu w (hSmallSubset hw)
      have hzBound := hKernelBound u hu z hzClosed
      rw [Metric.mem_closedBall]
      calc
        dist (f w) (f z) <= norm (f w) + norm (f z) := by
          simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
        _ <= nicolasJLargeMajorantAtDistance d u +
            nicolasJLargeMajorantAtDistance d u :=
          add_le_add hwBound hzBound
        _ = 2 * nicolasJLargeMajorantAtDistance d u := by ring
    have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
      hDiff hMaps (by dsimp [r]; linarith)
    change norm (deriv f z) <=
      (8 / R) * nicolasJLargeMajorantAtDistance d u
    calc
      norm (deriv f z) <=
          (2 * nicolasJLargeMajorantAtDistance d u) / r := hCauchy
      _ = (8 / R) * nicolasJLargeMajorantAtDistance d u := by
        dsimp [r]
        field_simp [hRPos.ne']
        ring
  let s : Set Complex := Metric.ball center (R / 4)
  have hHasDeriv : forall z : Complex, Membership.mem s z ->
      HasDerivAt nicolasJShiftedComplexContinuationFilledLarge
        (integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)) z := by
    intro z hz
    let F : Complex -> Real -> Complex := fun w => fun u =>
      nicolasJMellinShiftIntegrandFilled w u
    let F' : Complex -> Real -> Complex := fun w => fun u =>
      deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
    have hsNhd : Membership.mem (nhds z) s :=
      Metric.isOpen_ball.mem_nhds hz
    have hFMeas : Filter.Eventually
        (fun w : Complex => AEStronglyMeasurable (F w)
          (volume.restrict (Ioi (1 : Real)))) (nhds z) := by
      filter_upwards [hsNhd] with w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [F]
      exact (hContinuousU w hwClosed).aestronglyMeasurable measurableSet_Ioi
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      have hzDist : dist z center < R / 4 := by
        simpa [s, Metric.mem_ball] using hz
      linarith
    have hFInt : Integrable (F z)
        (volume.restrict (Ioi (1 : Real))) := by
      apply Integrable.mono'
        (nicolasJLargeMajorantAtDistance_integrableOn hd)
        ((hContinuousU z hzClosed).aestronglyMeasurable measurableSet_Ioi)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hKernelBound u hu z hzClosed
    have hF'Meas : AEStronglyMeasurable (F' z)
        (volume.restrict (Ioi (1 : Real))) := by
      dsimp [F']
      exact hDerivativeMeasurable z hz
    have hBound : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          norm (F' w u) <=
            (8 / R) * nicolasJLargeMajorantAtDistance d u)
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro w hw
      exact hDerivativeBound u hu w hw
    have hBoundInt : IntegrableOn
        (fun u : Real => (8 / R) * nicolasJLargeMajorantAtDistance d u)
        (Ioi (1 : Real)) :=
      (nicolasJLargeMajorantAtDistance_integrableOn hd).const_mul (8 / R)
    have hDiff : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          HasDerivAt (fun v : Complex => F v u) (F' w u) w)
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [F, F']
      exact (hAnalytic u hu w hwClosed).differentiableAt.hasDerivAt
    have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F')
      (bound := fun u : Real =>
        (8 / R) * nicolasJLargeMajorantAtDistance d u)
      hsNhd hFMeas hFInt hF'Meas hBound hBoundInt hDiff
    unfold nicolasJShiftedComplexContinuationFilledLarge
    simpa [F, F'] using hMain.2
  have hDiffOn : DifferentiableOn Complex
      nicolasJShiftedComplexContinuationFilledLarge s := by
    intro z hz
    exact (hHasDeriv z hz).differentiableAt.differentiableWithinAt
  apply hDiffOn.analyticAt
  dsimp [s]
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith : 0 < R / 4))

end

end Robin1984

