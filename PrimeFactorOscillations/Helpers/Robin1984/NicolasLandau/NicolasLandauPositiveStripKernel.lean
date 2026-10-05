/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauPositiveStrip.lean
Original source lines 25-440. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.Analytic.RiemannZetaRealNonzero
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauCompactBlock

/-!
# Uniform neighborhoods for the positive real shift

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_of_ne_zero_of_factor_ne_zero
    {s : Complex} (hsZero : Not (s = 0))
    (hFactor : Not (nicolasZetaPoleFactor s = 0)) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled s := by
  unfold nicolasPsiMellinTailContinuationFilled
  exact (nicolasPsiMellinContinuationFilled_analyticAt hsZero hFactor).sub
    (nicolasPsiMellinStartup_three_analyticAt s)

theorem eventually_nicolasZetaPoleFactor_ne_zero_shift_pos_real
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not (nicolasZetaPoleFactor
          (((u + 1 : Real) : Complex) - z) = 0))
      (nhds (sigma : Complex)) := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro u hu
  have hCenterPos : 0 < u + 1 - sigma := by
    linarith [hu.1]
  have hCenter : Not (nicolasZetaPoleFactor
      ((((u + 1 - sigma : Real) : Complex))) = 0) :=
    nicolasZetaPoleFactor_ne_zero_of_pos_real hCenterPos
  let G : Prod Complex Real -> Complex := fun p =>
    nicolasZetaPoleFactor (((p.2 + 1 : Real) : Complex) - p.1)
  have hGContinuous : Continuous G := by
    dsimp [G]
    exact nicolasZetaPoleFactor_differentiable.continuous.comp (by fun_prop)
  have hGCenter : Not (G ((sigma : Complex), u) = 0) := by
    dsimp [G]
    simpa using hCenter
  exact hGContinuous.continuousAt.eventually_ne hGCenter

theorem nicolasJMellinShiftIntegrandFilled_joint_continuousAt
    {u : Real} (hu : 0 <= u) {z : Complex}
    (hzZero : Not (z = 0))
    (hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0))
    (hFactor : Not (nicolasZetaPoleFactor
      (((u + 1 : Real) : Complex) - z) = 0)) :
    ContinuousAt (fun p : Prod Real Complex =>
      nicolasJMellinShiftIntegrandFilled p.2 p.1) (u, z) := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0Pos : 0 < u + 1 := by linarith
  have hTail0 : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s0 := by
    simpa [s0] using
      nicolasPsiMellinTailContinuationFilled_analyticAt_pos_real hs0Pos
  have hTail1 : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s1 := by
    exact
      nicolasPsiMellinTailContinuationFilled_analyticAt_of_ne_zero_of_factor_ne_zero
        (by simpa [s1, s0] using hShiftZero)
        (by simpa [s1, s0] using hFactor)
  let S0 : Prod Real Complex -> Complex := fun p =>
    ((p.1 + 1 : Real) : Complex)
  let S1 : Prod Real Complex -> Complex := fun p => S0 p - p.2
  have hS0 : Continuous S0 := by
    dsimp [S0]
    fun_prop
  have hS1 : Continuous S1 := by
    dsimp [S1]
    exact hS0.sub continuous_snd
  have hTail0Comp : ContinuousAt (fun p : Prod Real Complex =>
      nicolasPsiMellinTailContinuationFilled (S0 p)) (u, z) := by
    have hAt : ContinuousAt nicolasPsiMellinTailContinuationFilled
        (S0 (u, z)) := by
      simpa [S0, s0] using hTail0.continuousAt
    exact hAt.comp' hS0.continuousAt
  have hTail1Comp : ContinuousAt (fun p : Prod Real Complex =>
      nicolasPsiMellinTailContinuationFilled (S1 p)) (u, z) := by
    have hAt : ContinuousAt nicolasPsiMellinTailContinuationFilled
        (S1 (u, z)) := by
      simpa [S1, S0, s1, s0] using hTail1.continuousAt
    exact hAt.comp' hS1.continuousAt
  have hPower : Continuous (fun p : Prod Real Complex =>
      (3 : Complex) ^ p.2) := by
    fun_prop
  let raw : Prod Real Complex -> Complex := fun p =>
    ((p.1 + 1 : Real) : Complex) * Inv.inv (p.2 - 0) *
      (nicolasJShiftNumeratorFilled p.1 p.2 -
        nicolasJShiftNumeratorFilled p.1 0)
  have hNumerator : ContinuousAt (fun p : Prod Real Complex =>
      nicolasJShiftNumeratorFilled p.1 p.2) (u, z) := by
    unfold nicolasJShiftNumeratorFilled
    change ContinuousAt (fun p : Prod Real Complex =>
      nicolasPsiMellinTailContinuationFilled (S1 p) -
        (3 : Complex) ^ p.2 *
          nicolasPsiMellinTailContinuationFilled (S0 p)) (u, z)
    exact hTail1Comp.sub (hPower.continuousAt.mul hTail0Comp)
  have hNumeratorZero : ContinuousAt (fun p : Prod Real Complex =>
      nicolasJShiftNumeratorFilled p.1 0) (u, z) := by
    have hEq : (fun p : Prod Real Complex =>
        nicolasJShiftNumeratorFilled p.1 0) = fun _ => 0 := by
      funext p
      exact nicolasJShiftNumeratorFilled_zero p.1
    rw [hEq]
    exact continuousAt_const
  have hRaw : ContinuousAt raw (u, z) := by
    dsimp [raw]
    have hInv : ContinuousAt (fun p : Prod Real Complex =>
        Inv.inv (p.2 - 0)) (u, z) := by
      have hDen : ContinuousAt (fun p : Prod Real Complex => p.2 - 0)
          (u, z) := continuousAt_snd.sub continuousAt_const
      have hDiv : ContinuousAt (fun p : Prod Real Complex =>
          (1 : Complex) / (p.2 - 0)) (u, z) :=
        continuousAt_const.div hDen (by simpa using hzZero)
      simpa [one_div] using hDiv
    have hU : Continuous (fun p : Prod Real Complex =>
        ((p.1 + 1 : Real) : Complex)) := by
      fun_prop
    exact (hU.continuousAt.mul hInv).mul
      (hNumerator.sub hNumeratorZero)
  have hSecondNe : Filter.Eventually
      (fun p : Prod Real Complex => Not (p.2 = 0)) (nhds (u, z)) := by
    have hSecondContinuous : ContinuousAt
        (fun p : Prod Real Complex => p.2) (u, z) := continuousAt_snd
    exact hSecondContinuous.eventually_ne hzZero
  have hEq : Filter.EventuallyEq (nhds (u, z))
      (fun p : Prod Real Complex =>
        nicolasJMellinShiftIntegrandFilled p.2 p.1) raw := by
    filter_upwards [hSecondNe] with p hp
    unfold nicolasJMellinShiftIntegrandFilled raw
    rw [dslope_of_ne _ hp]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub]
    ring
  exact hRaw.congr_of_eventuallyEq hEq

theorem nicolasJMellinShiftIntegrandFilled_analyticAt_of_ne_zero_of_factor_ne_zero
    {u : Real} (hu : 0 <= u) {z : Complex}
    (hzZero : Not (z = 0))
    (hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0))
    (hFactor : Not (nicolasZetaPoleFactor
      (((u + 1 : Real) : Complex) - z) = 0)) :
    AnalyticAt Complex (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0Pos : 0 < u + 1 := by linarith
  have hTail0 : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s0 := by
    simpa [s0] using
      nicolasPsiMellinTailContinuationFilled_analyticAt_pos_real hs0Pos
  have hTail1 : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s1 :=
    nicolasPsiMellinTailContinuationFilled_analyticAt_of_ne_zero_of_factor_ne_zero
      (by simpa [s1, s0] using hShiftZero)
      (by simpa [s1, s0] using hFactor)
  have hAffine : AnalyticAt Complex (fun w : Complex => s0 - w) z :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s0 - w)) z := by
    have hComp := hTail1.comp_of_eq hAffine (by simp [s1])
    exact hComp.congr (Eventually.of_forall (fun _ => rfl))
  have hPower : AnalyticAt Complex (fun w : Complex =>
      (3 : Complex) ^ w) z := by
    have hDiff : Differentiable Complex (fun w : Complex =>
        (3 : Complex) ^ w) := by
      intro w
      exact DifferentiableAt.const_cpow differentiableAt_id
        (Or.inl (by norm_num))
    exact hDiff.analyticAt z
  have hNumerator : AnalyticAt Complex
      (nicolasJShiftNumeratorFilled u) z := by
    unfold nicolasJShiftNumeratorFilled
    exact hShift.sub (hPower.mul analyticAt_const)
  let raw : Complex -> Complex := fun w =>
    ((u + 1 : Real) : Complex) *
      slope (nicolasJShiftNumeratorFilled u) 0 w
  have hRaw : AnalyticAt Complex raw z := by
    have hDifference : AnalyticAt Complex (fun w : Complex =>
        nicolasJShiftNumeratorFilled u w -
          nicolasJShiftNumeratorFilled u 0) z :=
      hNumerator.sub analyticAt_const
    have hDenominator : AnalyticAt Complex (fun w : Complex => w - 0) z :=
      analyticAt_id.sub analyticAt_const
    have hQuotient := hDifference.div hDenominator
      (sub_ne_zero.mpr hzZero)
    have hDiv : AnalyticAt Complex (fun w : Complex =>
        ((u + 1 : Real) : Complex) *
          ((nicolasJShiftNumeratorFilled u w -
            nicolasJShiftNumeratorFilled u 0) / (w - 0))) z :=
      analyticAt_const.mul hQuotient
    have hRawEq : Filter.EventuallyEq (nhds z) raw
        (fun w : Complex => ((u + 1 : Real) : Complex) *
          ((nicolasJShiftNumeratorFilled u w -
            nicolasJShiftNumeratorFilled u 0) / (w - 0))) :=
      Eventually.of_forall (fun w => by
        unfold raw slope
        simp only [smul_eq_mul, vsub_eq_sub, div_eq_mul_inv]
        ring)
    exact (analyticAt_congr hRawEq).mpr hDiv
  have hEq : Filter.EventuallyEq (nhds z)
      (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u) raw := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hzZero] with w hw
    unfold nicolasJMellinShiftIntegrandFilled raw
    rw [dslope_of_ne _ hw]
  exact (analyticAt_congr hEq).mpr hRaw

theorem exists_nicolasPositiveCompactTubeRadius
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    Exists fun R : Real => And (0 < R)
      (forall z : Complex,
        Membership.mem (Metric.ball (sigma : Complex) R) z ->
          And (Not (z = 0))
            (And (dist z (sigma : Complex) < 1 / 4)
              (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
                Not (nicolasZetaPoleFactor
                  (((u + 1 : Real) : Complex) - z) = 0)))) := by
  have hTube := eventually_nicolasZetaPoleFactor_ne_zero_shift_pos_real
    hSigmaPos hSigma
  have hSigmaNe : Not ((sigma : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hSigmaPos.ne'
  have hZero : Filter.Eventually (fun z : Complex => Not (z = 0))
      (nhds (sigma : Complex)) :=
    continuousAt_id.eventually_ne hSigmaNe
  have hNear : Filter.Eventually (fun z : Complex =>
      dist z (sigma : Complex) < 1 / 4) (nhds (sigma : Complex)) := by
    exact Metric.ball_mem_nhds (sigma : Complex) (by norm_num)
  have hAll := (hTube.and hZero).and hNear
  choose R hRPos hR using Metric.mem_nhds_iff.1 hAll
  refine Exists.intro R (And.intro hRPos ?_)
  intro z hz
  have hAt := hR hz
  exact And.intro hAt.1.2 (And.intro hAt.2 hAt.1.1)

theorem exists_nicolasPositiveCompactKernelBound
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    Exists fun R : Real => Exists fun M : Real =>
      And (0 < R) (And (0 <= M)
        (And
          (forall z : Complex,
            Membership.mem (Metric.ball (sigma : Complex) R) z ->
              And (Not (z = 0))
                (And (dist z (sigma : Complex) < 1 / 4)
                  (forall u : Real,
                    Membership.mem (Icc (0 : Real) 1) u ->
                      Not (nicolasZetaPoleFactor
                        (((u + 1 : Real) : Complex) - z) = 0))))
          (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
            forall z : Complex,
              Membership.mem
                (Metric.closedBall (sigma : Complex) (R / 2)) z ->
                norm (nicolasJMellinShiftIntegrandFilled z u) <= M))) := by
  choose R hRPos hR using
    exists_nicolasPositiveCompactTubeRadius hSigmaPos hSigma
  let K : Set (Prod Real Complex) := fun p =>
    And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem
        (Metric.closedBall (sigma : Complex) (R / 2)) p.2)
  let F : Prod Real Complex -> Complex := fun p =>
    nicolasJMellinShiftIntegrandFilled p.2 p.1
  have hKCompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_Icc : IsCompact (Icc (0 : Real) 1)).prod
      (isCompact_closedBall (sigma : Complex) (R / 2))
  have hKNonempty : K.Nonempty := by
    refine Exists.intro ((0 : Real), (sigma : Complex)) ?_
    dsimp [K]
    exact And.intro (And.intro le_rfl zero_le_one)
      (Metric.mem_closedBall_self (by linarith))
  have hContinuous : ContinuousOn F K := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    have hpU : Membership.mem (Icc (0 : Real) 1) p.1 := hp.1
    have hpZClosed : Membership.mem
        (Metric.closedBall (sigma : Complex) (R / 2)) p.2 := hp.2
    have hpZBall : Membership.mem
        (Metric.ball (sigma : Complex) R) p.2 := by
      rw [Metric.mem_closedBall] at hpZClosed
      rw [Metric.mem_ball]
      linarith
    have hpGood := hR p.2 hpZBall
    have hReDiff : abs (p.2.re - sigma) <=
        dist p.2 (sigma : Complex) := by
      rw [dist_eq_norm]
      simpa using Complex.abs_re_le_norm (p.2 - (sigma : Complex))
    have hpZRe : p.2.re < sigma + 1 / 4 := by
      have hAbs : abs (p.2.re - sigma) < 1 / 4 :=
        lt_of_le_of_lt hReDiff hpGood.2.1
      have hUpper : p.2.re - sigma < 1 / 4 :=
        lt_of_le_of_lt (le_abs_self _) hAbs
      linarith
    have hShiftZero : Not
        ((((p.1 + 1 : Real) : Complex) - p.2) = 0) := by
      intro hZero
      have hReZero := congrArg Complex.re hZero
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hReZero
      linarith [hpU.1]
    exact nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      hpU.1 hpGood.1 hShiftZero (hpGood.2.2 p.1 hpU)
  choose p hpK hpMax using hKCompact.exists_isMaxOn hKNonempty hContinuous.norm
  let M : Real := norm (F p)
  refine Exists.intro R (Exists.intro M
    (And.intro hRPos (And.intro (norm_nonneg _) (And.intro hR ?_))))
  intro u hu z hz
  have hPair : K (u, z) := by
    dsimp [K]
    exact And.intro hu hz
  have hBound := hpMax hPair
  simpa [M, F] using hBound

theorem nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
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
      (Metric.closedBall (sigma : Complex) (R / 2)) z) :
    ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
  have hzBall : Membership.mem
      (Metric.ball (sigma : Complex) R) z := by
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  have hzGood := hGood z hzBall
  have hReDiff : abs (z.re - sigma) <= dist z (sigma : Complex) := by
    rw [dist_eq_norm]
    simpa using Complex.abs_re_le_norm (z - (sigma : Complex))
  have hzRe : z.re < sigma + 1 / 4 := by
    have hAbs : abs (z.re - sigma) < 1 / 4 :=
      lt_of_le_of_lt hReDiff hzGood.2.1
    have hUpper : z.re - sigma < 1 / 4 :=
      lt_of_le_of_lt (le_abs_self _) hAbs
    linarith
  intro u hu
  have hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
    intro hZero
    have hReZero := congrArg Complex.re hZero
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hReZero
    linarith [hu.1]
  have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
    hu.1 hzGood.1 hShiftZero (hzGood.2.2 u hu)
  have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
    fun_prop
  have hComp := hJoint.comp_of_eq hEmbed (by rfl)
  have hAt : ContinuousAt (fun v : Real =>
      nicolasJMellinShiftIntegrandFilled z v) u := by
    simpa [Function.comp_def] using hComp
  exact hAt.continuousWithinAt

def nicolasCompactStripDerivativeStep (R : Real) (n : Nat) : Complex :=
  (R : Complex) * nicolasJDerivativeStep n

theorem nicolasCompactStripDerivativeStep_ne_zero
    {R : Real} (hRPos : 0 < R) (n : Nat) :
    Not (nicolasCompactStripDerivativeStep R n = 0) := by
  unfold nicolasCompactStripDerivativeStep
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hRPos.ne')
    (nicolasJDerivativeStep_ne_zero n)

theorem norm_nicolasCompactStripDerivativeStep_le
    {R : Real} (hRPos : 0 < R) (n : Nat) :
    norm (nicolasCompactStripDerivativeStep R n) <= R / 8 := by
  unfold nicolasCompactStripDerivativeStep
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRPos]
  calc
    R * norm (nicolasJDerivativeStep n) <= R * (1 / 8 : Real) :=
      mul_le_mul_of_nonneg_left (norm_nicolasJDerivativeStep_lt n) hRPos.le
    _ = R / 8 := by ring

theorem nicolasCompactStripDerivativeStep_tendsto_zero
    (R : Real) :
    Tendsto (nicolasCompactStripDerivativeStep R) atTop
      (nhds (0 : Complex)) := by
  have hConst : Tendsto (fun _ : Nat => (R : Complex)) atTop
      (nhds (R : Complex)) := tendsto_const_nhds
  have h := hConst.mul nicolasJDerivativeStep_tendsto_zero
  unfold nicolasCompactStripDerivativeStep
  simpa using h

theorem nicolasJMellinShiftIntegrandFilled_analyticAt_of_compactTube
    {sigma R : Real} (hSigma : sigma < 1 / 2) (hRPos : 0 < R)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball (sigma : Complex) R) z ->
        And (Not (z = 0))
          (And (dist z (sigma : Complex) < 1 / 4)
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0))))
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (sigma : Complex) (R / 2)) z) :
    AnalyticAt Complex (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z := by
  have hzBall : Membership.mem
      (Metric.ball (sigma : Complex) R) z := by
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  have hzGood := hGood z hzBall
  have hReDiff : abs (z.re - sigma) <= dist z (sigma : Complex) := by
    rw [dist_eq_norm]
    simpa using Complex.abs_re_le_norm (z - (sigma : Complex))
  have hzRe : z.re < sigma + 1 / 4 := by
    have hAbs : abs (z.re - sigma) < 1 / 4 :=
      lt_of_le_of_lt hReDiff hzGood.2.1
    have hUpper : z.re - sigma < 1 / 4 :=
      lt_of_le_of_lt (le_abs_self _) hAbs
    linarith
  have hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
    intro hZero
    have hReZero := congrArg Complex.re hZero
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hReZero
    linarith [hu.1]
  exact
    nicolasJMellinShiftIntegrandFilled_analyticAt_of_ne_zero_of_factor_ne_zero
      hu.1 hzGood.1 hShiftZero (hzGood.2.2 u hu)

end

end Robin1984

