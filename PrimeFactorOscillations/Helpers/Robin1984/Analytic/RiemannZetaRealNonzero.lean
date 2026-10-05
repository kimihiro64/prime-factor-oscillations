/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/Analytic/RiemannZetaRealNonzero.lean
Original source lines 743-1098. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.Analytic.RiemannZetaRealBounds

/-!
# Analytic large-tail continuation on the positive real interval

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory Set

noncomputable section

theorem norm_deriv_nicolasJMellinShiftIntegrandFilled_le_half
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    norm (deriv (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z) <=
      8 * nicolasJLargeMajorantHalf u := by
  let f : Complex -> Complex := fun w : Complex =>
    nicolasJMellinShiftIntegrandFilled w u
  let R : Real := 1 / 4
  let M : Real := nicolasJLargeMajorantHalf u
  have hSmallSubset : Metric.ball z R <=
      Metric.ball (0 : Complex) (3 / 4 : Real) := by
    intro w hw
    rw [Metric.mem_ball] at hw hz
    rw [Metric.mem_ball]
    calc
      dist w 0 <= dist w z + dist z 0 := dist_triangle w z 0
      _ < (1 / 4 : Real) + (1 / 2 : Real) := add_lt_add hw hz
      _ = (3 / 4 : Real) := by norm_num
  have hzOuter : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self (by norm_num)
  have hDiff : DifferentiableOn Complex f (Metric.ball z R) :=
    (nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter hu).mono
      hSmallSubset
  have hMaps : MapsTo f (Metric.ball z R)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwOuter := hSmallSubset hw
    have hwBound : norm (f w) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorantHalf] using
        norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter hu hwOuter
    have hzBound : norm (f z) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorantHalf] using
        norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter hu hzOuter
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) <= norm (f w) + norm (f z) := by
        simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
      _ <= M + M := add_le_add hwBound hzBound
      _ = 2 * M := by ring
  have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
    hDiff hMaps (by norm_num : 0 < R)
  change norm (deriv f z) <= 8 * M
  calc
    norm (deriv f z) <= (2 * M) / R := hCauchy
    _ = 8 * M := by
      dsimp [R]
      ring

def nicolasJLargeDerivativeMajorantHalf (u : Real) : Real :=
  8 * nicolasJLargeMajorantHalf u

theorem nicolasJLargeDerivativeMajorantHalf_integrableOn :
    IntegrableOn nicolasJLargeDerivativeMajorantHalf (Ioi (1 : Real)) := by
  unfold nicolasJLargeDerivativeMajorantHalf
  exact nicolasJLargeMajorantHalf_integrableOn.const_mul 8

theorem nicolasJShiftNumeratorFilled_continuousOn_u_threeQuarter
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z) :
    ContinuousOn (fun u : Real => nicolasJShiftNumeratorFilled u z)
      (Ioi (1 : Real)) := by
  let s0 : Real -> Complex := fun u : Real => ((u + 1 : Real) : Complex)
  let s1 : Real -> Complex := fun u : Real => s0 u - z
  have hS0 : Continuous s0 := by
    dsimp [s0]
    fun_prop
  have hS1 : Continuous s1 := by
    dsimp [s1]
    exact hS0.sub continuous_const
  intro u hu
  have huOne : 1 < u := mem_Ioi.mp hu
  have hzNorm : norm z < (3 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (3 / 4 : Real) :=
    (Complex.re_le_norm z).trans_lt hzNorm
  have hs0 : 1 < (s0 u).re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < (s1 u).re := by
    dsimp [s1, s0]
    linarith
  have hTail0 : ContinuousAt (fun v : Real =>
      nicolasPsiMellinTailContinuationFilled (s0 v)) u :=
    (nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs0).continuousAt.comp
      hS0.continuousAt
  have hTail1 : ContinuousAt (fun v : Real =>
      nicolasPsiMellinTailContinuationFilled (s1 v)) u :=
    (nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs1).continuousAt.comp
      hS1.continuousAt
  unfold nicolasJShiftNumeratorFilled
  change ContinuousWithinAt (fun v : Real =>
    nicolasPsiMellinTailContinuationFilled (s1 v) -
      (3 : Complex) ^ z *
        nicolasPsiMellinTailContinuationFilled (s0 v))
    (Ioi (1 : Real)) u
  exact (hTail1.sub (continuousAt_const.mul hTail0)).continuousWithinAt

theorem nicolasJMellinShiftIntegrandFilled_continuousOn_u_threeQuarter_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z)
    (hzZero : Not (z = 0)) :
    ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hNumeratorZ :=
    nicolasJShiftNumeratorFilled_continuousOn_u_threeQuarter hz
  have hZeroMem : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) (0 : Complex) :=
    Metric.mem_ball_self (by norm_num)
  have hNumeratorZero :=
    nicolasJShiftNumeratorFilled_continuousOn_u_threeQuarter hZeroMem
  have hU : Continuous (fun u : Real => ((u + 1 : Real) : Complex)) := by
    fun_prop
  have hInv : Continuous (fun _ : Real => Inv.inv (z - 0)) :=
    continuous_const
  have hEq : (fun u : Real => nicolasJMellinShiftIntegrandFilled z u) =
      (fun u : Real => ((u + 1 : Real) : Complex) *
        Inv.inv (z - 0) *
          (nicolasJShiftNumeratorFilled u z -
            nicolasJShiftNumeratorFilled u 0)) := by
    funext u
    unfold nicolasJMellinShiftIntegrandFilled
    rw [dslope_of_ne _ hzZero]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub]
    ring
  rw [hEq]
  exact (hU.continuousOn.mul hInv.continuousOn).mul
    (hNumeratorZ.sub hNumeratorZero)

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero
  case neg =>
    have hzOuter : Membership.mem
        (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
      rw [Metric.mem_ball, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact
      (nicolasJMellinShiftIntegrandFilled_continuousOn_u_threeQuarter_of_ne
        hzOuter hzZero).aestronglyMeasurable measurableSet_Ioi

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_threeQuarter
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero
  case neg =>
    exact
      (nicolasJMellinShiftIntegrandFilled_continuousOn_u_threeQuarter_of_ne
        hz hzZero).aestronglyMeasurable measurableSet_Ioi

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_large_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hzOuter : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  apply Integrable.mono' nicolasJLargeMajorantHalf_integrableOn
    (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half hz)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa [nicolasJLargeMajorantHalf] using
    norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter
      (mem_Ioi.mp hu) hzOuter

theorem deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)
      (volume.restrict (Ioi (1 : Real))) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
      z (z + nicolasJDerivativeStep n)
  have hzNorm : norm z < (1 / 2 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzOuter : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hShiftOuter : forall n : Nat, Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real))
      (z + nicolasJDerivativeStep n) := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    calc
      norm (z + nicolasJDerivativeStep n) <=
          norm z + norm (nicolasJDerivativeStep n) := norm_add_le _ _
      _ < (1 / 2 : Real) + (1 / 8 : Real) :=
        add_lt_add_of_lt_of_le hzNorm (norm_nicolasJDerivativeStep_lt n)
      _ < (3 / 4 : Real) := by norm_num
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioi (1 : Real))) := by
    intro n
    have hShift :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_threeQuarter
        (hShiftOuter n)
    have hBase :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_threeQuarter
        hzOuter
    have hEq : slopeSeq n = fun u : Real =>
        Inv.inv ((z + nicolasJDerivativeStep n) - z) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasJDerivativeStep n) u -
            nicolasJMellinShiftIntegrandFilled z u) := by
      funext u
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub]
    rw [hEq]
    exact ((hShift.sub hBase).const_mul
      (Inv.inv ((z + nicolasJDerivativeStep n) - z))).aemeasurable
  have hStepWithin : Tendsto nicolasJDerivativeStep atTop
      (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro nicolasJDerivativeStep_tendsto_zero
      (Eventually.of_forall (fun n : Nat =>
        Set.mem_compl_singleton_iff.mpr
          (nicolasJDerivativeStep_ne_zero n)))
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
        (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)))
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huOne : 1 < u := mem_Ioi.mp hu
    have hDiffAt : DifferentiableAt Complex
        (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u) z :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter
        huOne z hzOuter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hzOuter)
    have hSlope := hDiffAt.hasDerivAt.tendsto_slope_zero.comp hStepWithin
    change Tendsto (fun n : Nat =>
      Inv.inv (nicolasJDerivativeStep n) *
        (nicolasJMellinShiftIntegrandFilled
            (z + nicolasJDerivativeStep n) u -
          nicolasJMellinShiftIntegrandFilled z u))
      atTop (nhds (deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
    dsimp [slopeSeq]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
    exact hSlope
  exact
    (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    HasDerivAt nicolasJShiftedComplexContinuationFilledLarge
      (integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) z := by
  let s : Set Complex := Metric.ball (0 : Complex) (1 / 2 : Real)
  let F : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    nicolasJMellinShiftIntegrandFilled w u
  let F' : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
  have hsNhd : Membership.mem (nhds z) s := by
    dsimp [s]
    exact Metric.isOpen_ball.mem_nhds hz
  have hFMeas : Filter.Eventually
      (fun w : Complex => AEStronglyMeasurable (F w)
        (volume.restrict (Ioi (1 : Real)))) (nhds z) := by
    filter_upwards [hsNhd] with w hw
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half hw
  have hFInt : Integrable (F z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact nicolasJMellinShiftIntegrandFilled_integrableOn_large_half hz
  have hF'Meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half hz
  have hBound : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        norm (F' w u) <= nicolasJLargeDerivativeMajorantHalf u)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    dsimp [F', s]
    unfold nicolasJLargeDerivativeMajorantHalf
    exact norm_deriv_nicolasJMellinShiftIntegrandFilled_le_half
      (mem_Ioi.mp hu) hw
  have hDiff : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        HasDerivAt (fun v : Complex => F v u) (F' w u) w)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hwOuter : Membership.mem
        (Metric.ball (0 : Complex) (3 / 4 : Real)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hAt : DifferentiableAt Complex
        (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter
        (mem_Ioi.mp hu) w hwOuter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hwOuter)
    dsimp [F, F']
    exact hAt.hasDerivAt
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F')
    (bound := nicolasJLargeDerivativeMajorantHalf)
    hsNhd hFMeas hFInt hF'Meas hBound
    nicolasJLargeDerivativeMajorantHalf_integrableOn hDiff
  unfold nicolasJShiftedComplexContinuationFilledLarge
  simpa [F, F'] using hMain.2

theorem nicolasJShiftedComplexContinuationFilledLarge_differentiableOn_half :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilledLarge
      (Metric.ball (0 : Complex) (1 / 2 : Real)) := by
  intro z hz
  exact (nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt_half
    hz).differentiableAt.differentiableWithinAt

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_pos_real
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      (sigma : Complex) := by
  apply
    nicolasJShiftedComplexContinuationFilledLarge_differentiableOn_half.analyticAt
  apply Metric.isOpen_ball.mem_nhds
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hSigmaPos]
  exact hSigma

end

end Robin1984

