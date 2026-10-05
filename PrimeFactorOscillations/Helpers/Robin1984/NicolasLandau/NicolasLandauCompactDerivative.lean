/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauCompactBlock.lean
Original source lines 345-711. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauCompactKernel

/-!
# Integrable derivative control on the compact parameter block

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

theorem norm_deriv_nicolasJMellinShiftIntegrandFilled_le_compact
    {u : Real} (hu : Membership.mem (Ioc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    norm (deriv (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z) <=
      (2 * nicolasCompactIntegrandBound) /
        nicolasCompactZRadius := by
  let f : Complex -> Complex := fun w : Complex =>
    nicolasJMellinShiftIntegrandFilled w u
  let R : Real := nicolasCompactZRadius
  let M : Real := nicolasCompactIntegrandBound
  have hRPos : 0 < R := by
    dsimp [R]
    exact nicolasCompactZRadius_pos
  have hSmallSubset : Metric.ball z R <=
      Metric.ball (0 : Complex) (3 * R) := by
    intro w hw
    rw [Metric.mem_ball] at hw hz
    rw [Metric.mem_ball]
    calc
      dist w 0 <= dist w z + dist z 0 := dist_triangle w z 0
      _ < R + R := add_lt_add hw hz
      _ < 3 * R := by linarith
  have hzLarge : Membership.mem
      (Metric.ball (0 : Complex) (3 * R)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self hRPos
  have hDiff : DifferentiableOn Complex f (Metric.ball z R) :=
    (nicolasJMellinShiftIntegrandFilled_differentiableOn_compact hu).mono
      hSmallSubset
  have hMaps : MapsTo f (Metric.ball z R)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwLarge := hSmallSubset hw
    have hwBound : norm (f w) <= M := by
      dsimp [f, M, R] at hwLarge
      dsimp [f, M]
      simpa [nicolasCompactIntegrandBound] using
        norm_nicolasJMellinShiftIntegrandFilled_le_compact
          (And.intro hu.1.le hu.2) hwLarge
    have hzBound : norm (f z) <= M := by
      dsimp [f, M, R] at hzLarge
      dsimp [f, M]
      simpa [nicolasCompactIntegrandBound] using
        norm_nicolasJMellinShiftIntegrandFilled_le_compact
          (And.intro hu.1.le hu.2) hzLarge
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) <= norm (f w) + norm (f z) := by
        simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
      _ <= M + M := add_le_add hwBound hzBound
      _ = 2 * M := by ring
  have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
    hDiff hMaps hRPos
  change norm (deriv f z) <= (2 * M) / R
  exact hCauchy

theorem nicolasJShiftNumeratorFilled_continuousOn_compact_u
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z) :
    ContinuousOn (fun u : Real => nicolasJShiftNumeratorFilled u z)
      (Icc (0 : Real) 1) := by
  intro u hu
  have hJoint :=
    nicolasJShiftNumeratorFilled_continuousOn_compact (u, z)
      (And.intro hu hz)
  have hPair : ContinuousWithinAt (fun v : Real => (v, z))
      (Icc (0 : Real) 1) u :=
    (continuousAt_id.prodMk continuousAt_const).continuousWithinAt
  have hMaps : MapsTo (fun v : Real => (v, z))
      (Icc (0 : Real) 1) nicolasCompactNumeratorDomain := by
    intro v hv
    exact And.intro hv hz
  have hComp := ContinuousWithinAt.comp
    (f := fun v : Real => (v, z))
    (g := fun p : Prod Real Complex =>
      nicolasJShiftNumeratorFilled p.1 p.2)
    hJoint hPair hMaps
  simpa [Function.comp_def] using hComp

theorem nicolasJMellinShiftIntegrandFilled_continuousOn_compact_u_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z)
    (hzZero : Not (z = 0)) :
    ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (Icc (0 : Real) 1) := by
  have hZeroMem : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) (0 : Complex) := by
    rw [Metric.mem_closedBall, dist_self]
    exact (mul_pos (by norm_num) nicolasCompactZRadius_pos).le
  have hNumeratorZ :=
    nicolasJShiftNumeratorFilled_continuousOn_compact_u hz
  have hNumeratorZero :=
    nicolasJShiftNumeratorFilled_continuousOn_compact_u hZeroMem
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

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z)
    (hzZero : Not (z = 0)) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  have hContinuous :=
    nicolasJMellinShiftIntegrandFilled_continuousOn_compact_u_of_ne
      hz hzZero
  have hSubset : Ioc (0 : Real) 1 <= Icc (0 : Real) 1 := by
    intro u hu
    exact And.intro hu.1.le hu.2
  exact (hContinuous.mono hSubset).aestronglyMeasurable measurableSet_Ioc

def nicolasCompactDerivativeStep (n : Nat) : Complex :=
  (((nicolasCompactZRadius / 2) *
    ((1 : Real) / ((n : Real) + 1)) : Real) : Complex)

theorem nicolasCompactDerivativeStep_ne_zero (n : Nat) :
    Not (nicolasCompactDerivativeStep n = 0) := by
  unfold nicolasCompactDerivativeStep
  apply Complex.ofReal_ne_zero.mpr
  exact mul_ne_zero
    (div_ne_zero (ne_of_gt nicolasCompactZRadius_pos) (by norm_num))
    (div_ne_zero (by norm_num) (by positivity))

theorem norm_nicolasCompactDerivativeStep_lt (n : Nat) :
    norm (nicolasCompactDerivativeStep n) < nicolasCompactZRadius := by
  have hRadius := nicolasCompactZRadius_pos
  have hRecipPos : 0 < (1 : Real) / ((n : Real) + 1) := by
    positivity
  have hRecipLe : (1 : Real) / ((n : Real) + 1) <= 1 := by
    apply (div_le_one (by positivity)).2
    norm_num
  unfold nicolasCompactDerivativeStep
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (div_pos hRadius (by norm_num)) hRecipPos)]
  calc
    nicolasCompactZRadius / 2 * ((1 : Real) / ((n : Real) + 1)) <=
        nicolasCompactZRadius / 2 * 1 :=
      mul_le_mul_of_nonneg_left hRecipLe
        (div_nonneg hRadius.le (by norm_num))
    _ < nicolasCompactZRadius := by linarith

theorem nicolasCompactDerivativeStep_tendsto_zero :
    Tendsto nicolasCompactDerivativeStep atTop (nhds (0 : Complex)) := by
  have hRecip : Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hScaled : Tendsto
      (fun n : Nat => (nicolasCompactZRadius / 2) *
        ((1 : Real) / ((n : Real) + 1)))
      atTop (nhds ((nicolasCompactZRadius / 2) * 0)) :=
    tendsto_const_nhds.mul hRecip
  have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hScaled
  have hFunctions :
      Function.comp Complex.ofReal (fun n : Nat =>
        (nicolasCompactZRadius / 2) *
          ((1 : Real) / ((n : Real) + 1))) =
        nicolasCompactDerivativeStep := by
    funext n
    rfl
  have hTarget : Tendsto
      (Function.comp Complex.ofReal (fun n : Nat =>
        (nicolasCompactZRadius / 2) *
          ((1 : Real) / ((n : Real) + 1))))
      atTop (nhds (0 : Complex)) := by
    simpa using hCast
  rw [hFunctions] at hTarget
  exact hTarget

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_zero :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled 0 u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  have hZMem : forall n : Nat,
      Membership.mem
        (Metric.closedBall (0 : Complex)
          (3 * nicolasCompactZRadius))
        (nicolasCompactDerivativeStep n) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have hStep := norm_nicolasCompactDerivativeStep_lt n
    have hRadius := nicolasCompactZRadius_pos
    linarith
  have hMeas : forall n : Nat, AEMeasurable
      (fun u : Real => nicolasJMellinShiftIntegrandFilled
        (nicolasCompactDerivativeStep n) u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    intro n
    exact
      (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_of_ne
        (hZMem n) (nicolasCompactDerivativeStep_ne_zero n)).aemeasurable
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto
        (fun n : Nat => nicolasJMellinShiftIntegrandFilled
          (nicolasCompactDerivativeStep n) u)
        atTop (nhds (nicolasJMellinShiftIntegrandFilled 0 u)))
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      hu.1).continuousAt.tendsto.comp
        nicolasCompactDerivativeStep_tendsto_zero
  exact
    (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_zero
  case neg =>
    exact
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_of_ne
        hz hzZero

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_compact
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioc (0 : Real) 1) := by
  have hMajorant : IntegrableOn
      (fun _ : Real => nicolasCompactIntegrandBound)
      (Ioc (0 : Real) 1) := integrableOn_const measure_Ioc_lt_top.ne
  apply Integrable.mono' hMajorant
    (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
      (Metric.ball_subset_closedBall hz))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  simpa [nicolasCompactIntegrandBound] using
    norm_nicolasJMellinShiftIntegrandFilled_le_compact
      (And.intro hu.1.le hu.2) hz

def nicolasCompactDerivativeMajorant : Real :=
  (2 * nicolasCompactIntegrandBound) /
    nicolasCompactZRadius


theorem nicolasCompactDerivativeMajorant_integrableOn :
    IntegrableOn (fun _ : Real => nicolasCompactDerivativeMajorant)
      (Ioc (0 : Real) 1) :=
  integrableOn_const measure_Ioc_lt_top.ne

theorem deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
      z (z + nicolasCompactDerivativeStep n)
  have hzNorm : norm z < nicolasCompactZRadius := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzLarge : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hRadius := nicolasCompactZRadius_pos
    linarith
  have hShiftLarge : forall n : Nat,
      Membership.mem
        (Metric.closedBall (0 : Complex)
          (3 * nicolasCompactZRadius))
        (z + nicolasCompactDerivativeStep n) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (calc
        norm (z + nicolasCompactDerivativeStep n) <=
            norm z + norm (nicolasCompactDerivativeStep n) := norm_add_le _ _
        _ < nicolasCompactZRadius + nicolasCompactZRadius :=
          add_lt_add hzNorm (norm_nicolasCompactDerivativeStep_lt n)
        _ < 3 * nicolasCompactZRadius := by
          linarith [nicolasCompactZRadius_pos]).le
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    intro n
    have hShift :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
        (hShiftLarge n)
    have hBase :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
        hzLarge
    have hEq : slopeSeq n = fun u : Real =>
        Inv.inv ((z + nicolasCompactDerivativeStep n) - z) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasCompactDerivativeStep n) u -
            nicolasJMellinShiftIntegrandFilled z u) := by
      funext u
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub]
    rw [hEq]
    exact ((hShift.sub hBase).const_mul
      (Inv.inv ((z + nicolasCompactDerivativeStep n) - z))).aemeasurable
  have hStepWithin : Tendsto nicolasCompactDerivativeStep atTop
      (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro nicolasCompactDerivativeStep_tendsto_zero
      (Eventually.of_forall (fun n : Nat =>
        Set.mem_compl_singleton_iff.mpr
          (nicolasCompactDerivativeStep_ne_zero n)))
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
        (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)))
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hzLargeBall : Membership.mem
        (Metric.ball (0 : Complex)
          (3 * nicolasCompactZRadius)) z := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith [nicolasCompactZRadius_pos]
    have hDiffAt : DifferentiableAt Complex
        (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u) z :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_compact
        hu z hzLargeBall).differentiableAt
          (Metric.isOpen_ball.mem_nhds hzLargeBall)
    have hSlope := hDiffAt.hasDerivAt.tendsto_slope_zero.comp hStepWithin
    change Tendsto (fun n : Nat =>
      Inv.inv (nicolasCompactDerivativeStep n) *
        (nicolasJMellinShiftIntegrandFilled
            (z + nicolasCompactDerivativeStep n) u -
          nicolasJMellinShiftIntegrandFilled z u))
      atTop (nhds (deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
    dsimp [slopeSeq]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
    exact hSlope
  exact
    (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

end

end Robin1984

