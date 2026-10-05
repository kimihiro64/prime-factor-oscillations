/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauPositiveTail.lean
Original source lines 785-1282. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPositiveTailBounds

/-!
# Differentiation of the controlled large-parameter tail

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem norm_deriv_nicolasJMellinShiftIntegrandFilled_le
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    norm (deriv (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z) <=
      16 * nicolasJLargeMajorant u := by
  let f : Complex -> Complex := fun w : Complex =>
    nicolasJMellinShiftIntegrandFilled w u
  let R : Real := 1 / 8
  let M : Real := nicolasJLargeMajorant u
  have hSmallSubset : Metric.ball z R <=
      Metric.ball (0 : Complex) (1 / 4 : Real) := by
    intro w hw
    rw [Metric.mem_ball] at hw hz
    rw [Metric.mem_ball]
    calc
      dist w 0 <= dist w z + dist z 0 := dist_triangle w z 0
      _ < (1 / 8 : Real) + (1 / 8 : Real) := add_lt_add hw hz
      _ = (1 / 4 : Real) := by norm_num
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self (by norm_num)
  have hDiff : DifferentiableOn Complex f (Metric.ball z R) :=
    (nicolasJMellinShiftIntegrandFilled_differentiableOn_quarter hu).mono
      hSmallSubset
  have hMaps : MapsTo f (Metric.ball z R)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwQuarter := hSmallSubset hw
    have hwBound : norm (f w) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorant] using
        norm_nicolasJMellinShiftIntegrandFilled_le hu hwQuarter
    have hzBound : norm (f z) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorant] using
        norm_nicolasJMellinShiftIntegrandFilled_le hu hzQuarter
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) <= norm (f w) + norm (f z) := by
        simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
      _ <= M + M := add_le_add hwBound hzBound
      _ = 2 * M := by ring
  have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
    hDiff hMaps (by norm_num : 0 < R)
  change norm (deriv f z) <= 16 * M
  calc
    norm (deriv f z) <= (2 * M) / R := hCauchy
    _ = 16 * M := by
      dsimp [R]
      ring

theorem nicolasJShiftNumeratorFilled_continuousOn_u
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z) :
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
  have hzNorm : norm z < (1 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (1 / 4 : Real) :=
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

theorem nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z)
    (hzZero : Not (z = 0)) :
    ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hNumeratorZ := nicolasJShiftNumeratorFilled_continuousOn_u hz
  have hZeroMem : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) (0 : Complex) :=
    Metric.mem_ball_self (by norm_num)
  have hNumeratorZero :=
    nicolasJShiftNumeratorFilled_continuousOn_u hZeroMem
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

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z)
    (hzZero : Not (z = 0)) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) :=
  (nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_ne
    hz hzZero).aestronglyMeasurable measurableSet_Ioi

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled 0 u)
      (volume.restrict (Ioi (1 : Real))) := by
  let zseq : Nat -> Complex := fun n : Nat =>
    (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex)
  have hZPos : forall n : Nat,
      0 < (1 : Real) / (8 * ((n : Real) + 1)) := by
    intro n
    positivity
  have hZMem : forall n : Nat, Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) (zseq n) := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [zseq]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hZPos n)]
    have hn : 0 <= (n : Real) := by positivity
    apply one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 4)
    nlinarith
  have hZNe : forall n : Nat, Not (zseq n = 0) := by
    intro n
    dsimp [zseq]
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero (by norm_num) (by positivity))
  have hRecip : Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hScaled : Tendsto
      (fun n : Nat => (1 / 8 : Real) *
        ((1 : Real) / ((n : Real) + 1)))
      atTop (nhds ((1 / 8 : Real) * 0)) :=
    tendsto_const_nhds.mul hRecip
  have hReal : Tendsto
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1)))
      atTop (nhds 0) := by
    have hFunctions :
        (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1))) =
          (fun n : Nat => (1 / 8 : Real) *
            ((1 : Real) / ((n : Real) + 1))) := by
      funext n
      field_simp
    rw [hFunctions]
    simpa using hScaled
  have hZ : Tendsto zseq atTop (nhds (0 : Complex)) := by
    have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
    change Tendsto
      (fun n : Nat =>
        (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex))
      atTop (nhds (0 : Complex)) at hCast
    change Tendsto
      (fun n : Nat =>
        (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex))
      atTop (nhds (0 : Complex))
    exact hCast
  have hMeas : forall n : Nat, AEMeasurable
      (fun u : Real => nicolasJMellinShiftIntegrandFilled (zseq n) u)
      (volume.restrict (Ioi (1 : Real))) := by
    intro n
    exact (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne
      (hZMem n) (hZNe n)).aemeasurable
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto
        (fun n : Nat => nicolasJMellinShiftIntegrandFilled (zseq n) u)
        atTop (nhds (nicolasJMellinShiftIntegrandFilled 0 u)))
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huPos : 0 < u := zero_lt_one.trans hu
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      huPos).continuousAt.tendsto.comp hZ
  exact (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero
  case neg =>
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne
      hz hzZero

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_large
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  apply Integrable.mono' nicolasJLargeMajorant_integrableOn
    (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable hzQuarter)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa [nicolasJLargeMajorant] using
    norm_nicolasJMellinShiftIntegrandFilled_le (mem_Ioi.mp hu) hzQuarter

def nicolasJLargeDerivativeMajorant (u : Real) : Real :=
  16 * nicolasJLargeMajorant u

theorem nicolasJLargeDerivativeMajorant_integrableOn :
    IntegrableOn nicolasJLargeDerivativeMajorant (Ioi (1 : Real)) := by
  unfold nicolasJLargeDerivativeMajorant
  exact nicolasJLargeMajorant_integrableOn.const_mul 16

def nicolasJDerivativeStep (n : Nat) : Complex :=
  (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex)

theorem nicolasJDerivativeStep_ne_zero (n : Nat) :
    Not (nicolasJDerivativeStep n = 0) := by
  unfold nicolasJDerivativeStep
  exact Complex.ofReal_ne_zero.mpr
    (div_ne_zero (by norm_num) (by positivity))

theorem norm_nicolasJDerivativeStep_lt (n : Nat) :
    norm (nicolasJDerivativeStep n) <= (1 / 8 : Real) := by
  unfold nicolasJDerivativeStep
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity :
      0 < (1 : Real) / (8 * ((n : Real) + 1)))]
  apply one_div_le_one_div_of_le (by norm_num : (0 : Real) < 8)
  have hn : 0 <= (n : Real) := by positivity
  nlinarith

theorem nicolasJDerivativeStep_tendsto_zero :
    Tendsto nicolasJDerivativeStep atTop (nhds (0 : Complex)) := by
  have hRecip : Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hScaled : Tendsto
      (fun n : Nat => (1 / 8 : Real) *
        ((1 : Real) / ((n : Real) + 1)))
      atTop (nhds ((1 / 8 : Real) * 0)) :=
    tendsto_const_nhds.mul hRecip
  have hFunctions :
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1))) =
        (fun n : Nat => (1 / 8 : Real) *
          ((1 : Real) / ((n : Real) + 1))) := by
    funext n
    field_simp
  have hReal : Tendsto
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1)))
      atTop (nhds 0) := by
    rw [hFunctions]
    simpa using hScaled
  have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
  change Tendsto nicolasJDerivativeStep atTop (nhds (0 : Complex)) at hCast
  exact hCast

theorem deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)
      (volume.restrict (Ioi (1 : Real))) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
      z (z + nicolasJDerivativeStep n)
  have hzNorm : norm z < (1 / 8 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hShiftQuarter : forall n : Nat, Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real))
      (z + nicolasJDerivativeStep n) := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    calc
      norm (z + nicolasJDerivativeStep n) <=
          norm z + norm (nicolasJDerivativeStep n) := norm_add_le _ _
      _ < (1 / 8 : Real) + (1 / 8 : Real) :=
        add_lt_add_of_lt_of_le hzNorm (norm_nicolasJDerivativeStep_lt n)
      _ = (1 / 4 : Real) := by norm_num
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioi (1 : Real))) := by
    intro n
    have hShift :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
        (hShiftQuarter n)
    have hBase :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable hzQuarter
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
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_quarter
        huOne z hzQuarter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hzQuarter)
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
  exact (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

def nicolasJShiftedComplexContinuationFilledLarge (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (1 : Real)))
    (nicolasJMellinShiftIntegrandFilled z)

theorem nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    HasDerivAt nicolasJShiftedComplexContinuationFilledLarge
      (integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) z := by
  let s : Set Complex := Metric.ball (0 : Complex) (1 / 8 : Real)
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
    have hwQuarter : Membership.mem
        (Metric.ball (0 : Complex) (1 / 4 : Real)) w := by
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
      hwQuarter
  have hFInt : Integrable (F z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact nicolasJMellinShiftIntegrandFilled_integrableOn_large hz
  have hF'Meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable hz
  have hBound : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        norm (F' w u) <= nicolasJLargeDerivativeMajorant u)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    dsimp [F', s]
    unfold nicolasJLargeDerivativeMajorant
    exact norm_deriv_nicolasJMellinShiftIntegrandFilled_le
      (mem_Ioi.mp hu) hw
  have hDiff : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        HasDerivAt (fun v : Complex => F v u) (F' w u) w)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hwQuarter : Membership.mem
        (Metric.ball (0 : Complex) (1 / 4 : Real)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hAt : DifferentiableAt Complex
        (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_quarter
        (mem_Ioi.mp hu) w hwQuarter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hwQuarter)
    dsimp [F, F']
    exact hAt.hasDerivAt
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := nicolasJLargeDerivativeMajorant)
    hsNhd hFMeas hFInt hF'Meas hBound
    nicolasJLargeDerivativeMajorant_integrableOn hDiff
  unfold nicolasJShiftedComplexContinuationFilledLarge
  simpa [F, F'] using hMain.2

theorem nicolasJShiftedComplexContinuationFilledLarge_differentiableOn :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilledLarge
      (Metric.ball (0 : Complex) (1 / 8 : Real)) := by
  intro z hz
  exact (nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt
    hz).differentiableAt.differentiableWithinAt


theorem exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one :
    Exists fun r : Real => And (0 < r)
      (forall s : Complex, Membership.mem
        (Metric.ball (1 : Complex) r) s ->
          AnalyticAt Complex nicolasPsiMellinTailContinuationFilled s) := by
  have hEventually :=
    nicolasPsiMellinTailContinuationFilled_analyticAt_one.eventually_analyticAt
  choose r hrPos hrSubset using Metric.mem_nhds_iff.1 hEventually
  refine Exists.intro r (And.intro hrPos ?_)
  intro s hs
  exact hrSubset hs

theorem nicolasJMellinShiftIntegrandFilled_eq_raw
    {z : Complex} (hzRe : z.re < 0) {u : Real} (hu : 0 < u) :
    nicolasJMellinShiftIntegrandFilled z u =
      nicolasJMellinShiftIntegrand z u := by
  have hzZero : Not (z = 0) := by
    intro hZero
    rw [hZero] at hzRe
    norm_num at hzRe
  have hBaseRe : 1 < (((u + 1 : Real) : Complex)).re := by
    simp
    linarith
  have hShiftRe : 1 <
      ((((u + 1 : Real) : Complex) - z)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hBaseEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hBaseRe
  have hShiftEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hShiftRe
  unfold nicolasJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzZero]
  unfold slope
  rw [nicolasJShiftNumeratorFilled_zero]
  unfold nicolasJShiftNumeratorFilled nicolasJMellinShiftIntegrand
  rw [hBaseEq, hShiftEq]
  simp only [sub_zero, smul_eq_mul, vsub_eq_sub]
  field_simp [hzZero]

end

end Robin1984

