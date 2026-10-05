/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauCompactBlock.lean
Original source lines 712-1067. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauCompactDerivative

/-!
# The compact continuation and finite Mellin startup

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

def nicolasJShiftedComplexContinuationFilledCompact (z : Complex) : Complex :=
  integral (volume.restrict (Ioc (0 : Real) 1))
    (nicolasJMellinShiftIntegrandFilled z)

theorem nicolasJShiftedComplexContinuationFilledCompact_hasDerivAt
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    HasDerivAt nicolasJShiftedComplexContinuationFilledCompact
      (integral (volume.restrict (Ioc (0 : Real) 1)) (fun u : Real =>
        deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) z := by
  let s : Set Complex :=
    Metric.ball (0 : Complex) nicolasCompactZRadius
  let F : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    nicolasJMellinShiftIntegrandFilled w u
  let F' : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
  have hsNhd : Membership.mem (nhds z) s := by
    dsimp [s]
    exact Metric.isOpen_ball.mem_nhds hz
  have hFMeas : Filter.Eventually
      (fun w : Complex => AEStronglyMeasurable (F w)
        (volume.restrict (Ioc (0 : Real) 1))) (nhds z) := by
    filter_upwards [hsNhd] with w hw
    have hwLarge : Membership.mem
        (Metric.closedBall (0 : Complex)
          (3 * nicolasCompactZRadius)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith [nicolasCompactZRadius_pos]
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
      hwLarge
  have hzLarge : Membership.mem
      (Metric.ball (0 : Complex)
        (3 * nicolasCompactZRadius)) z := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith [nicolasCompactZRadius_pos]
  have hFInt : Integrable (F z)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    exact nicolasJMellinShiftIntegrandFilled_integrableOn_compact hzLarge
  have hF'Meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    exact deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
      hz
  have hBound : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        norm (F' w u) <= nicolasCompactDerivativeMajorant)
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    intro w hw
    dsimp [F', s] at hw
    dsimp [F']
    unfold nicolasCompactDerivativeMajorant
    exact norm_deriv_nicolasJMellinShiftIntegrandFilled_le_compact hu hw
  have hDiff : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        HasDerivAt (fun v : Complex => F v u) (F' w u) w)
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    intro w hw
    have hwLarge : Membership.mem
        (Metric.ball (0 : Complex)
          (3 * nicolasCompactZRadius)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith [nicolasCompactZRadius_pos]
    have hAt : DifferentiableAt Complex
        (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_compact
        hu w hwLarge).differentiableAt
          (Metric.isOpen_ball.mem_nhds hwLarge)
    dsimp [F, F']
    exact hAt.hasDerivAt
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F')
    (bound := fun _ : Real => nicolasCompactDerivativeMajorant)
    hsNhd hFMeas hFInt hF'Meas hBound
    nicolasCompactDerivativeMajorant_integrableOn hDiff
  unfold nicolasJShiftedComplexContinuationFilledCompact
  simpa [F, F'] using hMain.2

theorem nicolasJShiftedComplexContinuationFilledCompact_differentiableOn :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilledCompact
      (Metric.ball (0 : Complex) nicolasCompactZRadius) := by
  intro z hz
  exact
    (nicolasJShiftedComplexContinuationFilledCompact_hasDerivAt
      hz).differentiableAt.differentiableWithinAt


theorem nicolasJShiftedComplexContinuationFilled_eq_compact_add_large
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    nicolasJShiftedComplexContinuationFilled z =
      nicolasJShiftedComplexContinuationFilledCompact z +
        nicolasJShiftedComplexContinuationFilledLarge z := by
  have hzNorm : norm z < nicolasCompactZRadius := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzCompact : Membership.mem
      (Metric.ball (0 : Complex)
        (3 * nicolasCompactZRadius)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith [nicolasCompactZRadius_pos]
  have hzLarge : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    have hRadiusBound := nicolasCompactZRadius_le_one_sixty_four
    linarith
  have hCompactInt :=
    nicolasJMellinShiftIntegrandFilled_integrableOn_compact hzCompact
  have hLargeInt :=
    nicolasJMellinShiftIntegrandFilled_integrableOn_large hzLarge
  unfold nicolasJShiftedComplexContinuationFilled
    nicolasJShiftedComplexContinuationFilledCompact
    nicolasJShiftedComplexContinuationFilledLarge
  rw [<- Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) <= 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hCompactInt
  . exact hLargeInt

theorem nicolasJShiftedComplexContinuationFilled_differentiableOn_compactRadius :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilled
      (Metric.ball (0 : Complex) nicolasCompactZRadius) := by
  have hLargeSubset : Metric.ball (0 : Complex) nicolasCompactZRadius <=
      Metric.ball (0 : Complex) (1 / 8 : Real) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have hRadiusBound := nicolasCompactZRadius_le_one_sixty_four
    linarith
  have hSum : DifferentiableOn Complex
      (fun z : Complex =>
        nicolasJShiftedComplexContinuationFilledCompact z +
          nicolasJShiftedComplexContinuationFilledLarge z)
      (Metric.ball (0 : Complex) nicolasCompactZRadius) :=
    nicolasJShiftedComplexContinuationFilledCompact_differentiableOn.add
      (nicolasJShiftedComplexContinuationFilledLarge_differentiableOn.mono
        hLargeSubset)
  exact hSum.congr (fun z hz =>
    nicolasJShiftedComplexContinuationFilled_eq_compact_add_large hz)

theorem nicolasJShiftedComplexContinuationFilled_analyticAt_zero :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilled 0 := by
  apply
    nicolasJShiftedComplexContinuationFilled_differentiableOn_compactRadius.analyticAt
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self nicolasCompactZRadius_pos)

def nicolasJComplexMellinStartup (X : Real) (s : Complex) : Complex :=
  integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
    (x : Complex) ^ (s - 1) * (nicolasJ x : Complex))

theorem nicolasJComplexMellinStartup_differentiableAt
    {X : Real} (hX : 3 <= X) (s0 : Complex) :
    DifferentiableAt Complex (nicolasJComplexMellinStartup X) s0 := by
  let F : Complex -> Real -> Complex := fun s x =>
    (x : Complex) ^ (s - 1) * (nicolasJ x : Complex)
  let F' : Complex -> Real -> Complex := fun s x =>
    ((Real.log x : Real) : Complex) * F s x
  let base : Real -> Complex := fun x =>
    (x : Complex) ^ (-3 : Complex) * (nicolasJ x : Complex)
  let ratio : Complex -> Real -> Complex := fun s x =>
    (x : Complex) ^ (s + 2)
  let majorant : Real -> Real := fun x =>
    norm (base x) * X ^ (abs s0.re + 4)
  have hRealBase : IntegrableOn (fun x : Real =>
      x ^ (-3 : Real) * nicolasJ x) (Ioc (3 : Real) X) := by
    have h := nicolasJ_realMellin_integrableOn_Ioi_three
      (a := (-2 : Real)) (by norm_num)
    have hRestricted := h.mono_set
      (show Ioc (3 : Real) X <= Ioi 3 from Ioc_subset_Ioi_self)
    apply hRestricted.congr_fun
    . intro x hx
      congr 2
      norm_num
    . exact measurableSet_Ioc
  have hCastBase : IntegrableOn (fun x : Real =>
      ((x ^ (-3 : Real) * nicolasJ x : Real) : Complex))
      (Ioc (3 : Real) X) :=
    Complex.ofRealCLM.integrable_comp hRealBase
  have hBaseIntegrable : Integrable base
      (volume.restrict (Ioc (3 : Real) X)) := by
    apply hCastBase.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    dsimp [base]
    rw [show (-3 : Complex) = ((-3 : Real) : Complex) by norm_num,
      <- Complex.ofReal_cpow hxPos.le]
    push_cast
    rfl
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hMajorantIntegrable : Integrable majorant
      (volume.restrict (Ioc (3 : Real) X)) := by
    have h := hBaseIntegrable.norm.const_mul
      (X ^ (abs s0.re + 4))
    simpa [majorant, mul_comm] using h
  have hMeasurable : forall s : Complex, AEStronglyMeasurable (F s)
      (volume.restrict (Ioc (3 : Real) X)) := by
    intro s
    have hRatioContinuous : ContinuousOn (ratio s) (Ioc (3 : Real) X) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      dsimp [ratio]
      have hxPos : 0 < x := lt_trans (by norm_num) hx.1
      exact (continuousAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 hxPos)).comp
          Complex.continuous_ofReal.continuousAt
    have hProduct := hBaseIntegrable.aestronglyMeasurable.mul
      (hRatioContinuous.aestronglyMeasurable measurableSet_Ioc)
    apply hProduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hPower : (x : Complex) ^ (-3 : Complex) *
        (x : Complex) ^ (s + 2) = (x : Complex) ^ (s - 1) := by
      rw [<- Complex.cpow_add _ _ hxZero]
      congr 1
      ring
    dsimp [F, base, ratio]
    calc
      (x : Complex) ^ (-3 : Complex) * (nicolasJ x : Complex) *
          (x : Complex) ^ (s + 2) =
          ((x : Complex) ^ (-3 : Complex) *
            (x : Complex) ^ (s + 2)) * (nicolasJ x : Complex) := by ring
      _ = (x : Complex) ^ (s - 1) * (nicolasJ x : Complex) := by
        rw [hPower]
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall x : Real, 3 < x -> x <= X ->
        norm (F s x) <= majorant x := by
    intro s hs x hxThree hxX
    have hDist : norm (s - s0) < 1 := by
      simpa [dist_eq_norm] using hs
    have hReAbs : abs (s.re - s0.re) <= norm (s - s0) := by
      simpa using Complex.abs_re_le_norm (s - s0)
    have hReUpper : s.re < s0.re + 1 := by
      have hAbsLt : abs (s.re - s0.re) < 1 := lt_of_le_of_lt hReAbs hDist
      linarith [(abs_lt.mp hAbsLt).2]
    have hxPos : 0 < x := lt_trans (by norm_num) hxThree
    have hxOne : 1 <= x := by linarith
    have hExponent : s.re + 2 <= abs s0.re + 4 := by
      have hPosPart : s0.re <= abs s0.re := le_abs_self s0.re
      linarith
    have hExponentNonneg : 0 <= abs s0.re + 4 := by positivity
    have hRatioBound : norm (ratio s x) <=
        X ^ (abs s0.re + 4) := by
      dsimp [ratio]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
      calc
        x ^ (s.re + 2) <= x ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow_of_exponent_le hxOne hExponent
        _ <= X ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow hxPos.le hxX hExponentNonneg
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hFactor : F s x = base x * ratio s x := by
      have hPower : (x : Complex) ^ (-3 : Complex) *
          (x : Complex) ^ (s + 2) = (x : Complex) ^ (s - 1) := by
        rw [<- Complex.cpow_add _ _ hxZero]
        congr 1
        ring
      dsimp [F, base, ratio]
      calc
        (x : Complex) ^ (s - 1) * (nicolasJ x : Complex) =
            ((x : Complex) ^ (-3 : Complex) *
              (x : Complex) ^ (s + 2)) * (nicolasJ x : Complex) := by
          rw [hPower]
        _ = ((x : Complex) ^ (-3 : Complex) *
            (nicolasJ x : Complex)) * (x : Complex) ^ (s + 2) := by ring
    rw [hFactor, norm_mul]
    dsimp [majorant]
    exact mul_le_mul_of_nonneg_left hRatioBound (norm_nonneg (base x))
  have hFIntegrable : Integrable (F s0)
      (volume.restrict (Ioc (3 : Real) X)) := by
    apply Integrable.mono hMajorantIntegrable (hMeasurable s0)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hMajorantNonneg : 0 <= majorant x := by
      dsimp [majorant]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hMajorantNonneg]
    exact hBound s0 (by simp [dist_self]) x hx.1 hx.2
  have hDerivativeMeasurable : AEStronglyMeasurable (F' s0)
      (volume.restrict (Ioc (3 : Real) X)) := by
    have hRealLogOn : ContinuousOn (fun x : Real => Real.log x)
        (Ioc (3 : Real) X) := by
      apply Real.continuousOn_log.mono
      intro x hx
      exact Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (lt_trans (by norm_num) hx.1))
    have hRealLog : AEStronglyMeasurable (fun x : Real => Real.log x)
        (volume.restrict (Ioc (3 : Real) X)) :=
      hRealLogOn.aestronglyMeasurable measurableSet_Ioc
    have hLog : AEStronglyMeasurable
        (fun x : Real => ((Real.log x : Real) : Complex))
        (volume.restrict (Ioc (3 : Real) X)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hRealLog
    exact hLog.mul (hMeasurable s0)
  have hDerivativeBound : Filter.Eventually
      (fun x : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        norm (F' s x) <= X * majorant x)
      (ae (volume.restrict (Ioc (3 : Real) X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro s hs
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxOne : 1 <= x := by linarith [hx.1]
    have hLogNonneg : 0 <= Real.log x := Real.log_nonneg hxOne
    have hLogBound : Real.log x <= X := by
      have hLogSub := Real.log_le_sub_one_of_pos hxPos
      linarith [hx.2]
    have hFBound : norm (F s x) <= majorant x :=
      hBound s (by simpa [Metric.mem_ball] using hs) x hx.1 hx.2
    dsimp [F']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hLogNonneg]
    exact mul_le_mul hLogBound hFBound (norm_nonneg _) hXPos.le
  have hDerivativeIntegrable : Integrable (fun x : Real => X * majorant x)
      (volume.restrict (Ioc (3 : Real) X)) :=
    hMajorantIntegrable.const_mul X
  have hDerivative : Filter.Eventually
      (fun x : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        HasDerivAt (fun z : Complex => F z x) (F' s x) s)
      (ae (volume.restrict (Ioc (3 : Real) X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro s hs
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hExponent : HasDerivAt (fun z : Complex => z - 1) 1 s :=
      (hasDerivAt_id' s).sub_const 1
    have hPower := hExponent.const_cpow (Or.inl hxZero)
    have hProduct := hPower.mul_const (nicolasJ x : Complex)
    dsimp [F, F']
    apply hProduct.congr_deriv
    rw [Complex.ofReal_log hxPos.le]
    ring
  unfold nicolasJComplexMellinStartup
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s0 zero_lt_one)
    (Eventually.of_forall hMeasurable) hFIntegrable
    hDerivativeMeasurable hDerivativeBound hDerivativeIntegrable hDerivative
  exact hMain.2.differentiableAt

theorem nicolasJComplexMellinStartup_analyticAt
    {X : Real} (hX : 3 <= X) (s0 : Complex) :
    AnalyticAt Complex (nicolasJComplexMellinStartup X) s0 := by
  have hDifferentiable : Differentiable Complex
      (nicolasJComplexMellinStartup X) := by
    intro s
    exact nicolasJComplexMellinStartup_differentiableAt hX s
  exact hDifferentiable.analyticAt s0

end

end Robin1984

