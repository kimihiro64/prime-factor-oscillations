/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauRightmostRay.lean
Original source lines 495-855. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauRayIdentity

/-!
# Uniform control of the scaled endpoint kernel

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

def nicolasJRightmostRayTranslatedScaledKernel
    (rho : Complex) (eps v : Real) : Complex :=
  (v : Complex) * nicolasJMellinShiftIntegrand
    (nicolasRightmostRayPoint rho eps) (v - eps)

theorem nicolasJMellinShiftIntegrandFilled_eq_raw_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps u : Real} (hEps : 0 < eps) (hU : 0 < u) :
    nicolasJMellinShiftIntegrandFilled
        (nicolasRightmostRayPoint rho eps) u =
      nicolasJMellinShiftIntegrand
        (nicolasRightmostRayPoint rho eps) u := by
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hzZero : Not (nicolasRightmostRayPoint rho eps = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    unfold nicolasRightmostRayPoint at hEqIm
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.zero_im] at hEqIm
    apply hIm
    linarith
  let s : Complex := rho + ((eps + u : Real) : Complex)
  have hShift :
      (((u + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps) = s := by
    dsimp [s, nicolasRightmostRayPoint]
    push_cast
    ring
  have hsIm : s.im = rho.im := by
    dsimp [s]
    simp
  have hsZero : Not (s = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.zero_im] at hEqIm
    exact hIm hEqIm
  have hsOne : Not (s = 1) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.one_im] at hEqIm
    exact hIm hEqIm
  have hZeta : Not (riemannZeta s = 0) := by
    dsimp [s]
    exact hRay (eps + u) (by linarith)
  have hBaseRe : 1 < (((u + 1 : Real) : Complex)).re := by
    simp
    linarith
  have hBaseEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hBaseRe
  have hShiftEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw hsZero hsOne hZeta
  unfold nicolasJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzZero]
  unfold slope
  rw [nicolasJShiftNumeratorFilled_zero]
  unfold nicolasJShiftNumeratorFilled nicolasJMellinShiftIntegrand
  rw [hBaseEq, hShift, hShiftEq]
  simp only [sub_zero, smul_eq_mul, vsub_eq_sub]
  field_simp [hzZero]

def nicolasJRightmostRayTranslatedScaledKernelFilled
    (rho : Complex) (eps v : Real) : Complex :=
  (v : Complex) * nicolasJMellinShiftIntegrandFilled
    (nicolasRightmostRayPoint rho eps) (v - eps)

theorem nicolasJRightmostRayTranslatedScaledKernelFilled_eq_raw
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps v : Real} (hEps : 0 < eps) (hEpsV : eps < v) :
    nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v =
      nicolasJRightmostRayTranslatedScaledKernel rho eps v := by
  unfold nicolasJRightmostRayTranslatedScaledKernelFilled
    nicolasJRightmostRayTranslatedScaledKernel
  rw [nicolasJMellinShiftIntegrandFilled_eq_raw_rightmostRay
    hZero hHalf hOneRe hRay hEps (by linarith)]

theorem nicolasJRightmostRayTranslatedScaledKernel_tendsto
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Exists fun d : Complex => And (Not (d = 0))
      (Tendsto (fun p : Prod Real Real =>
          nicolasJRightmostRayTranslatedScaledKernel rho p.1 p.2)
        (nhdsWithin ((0 : Real), (0 : Real))
          {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)})
        (nhds d)) := by
  have hRhoZero : Not (rho = 0) := by
    intro hEq
    rw [hEq] at hHalf
    norm_num at hHalf
  have hRhoOne : Not (rho = 1) := by
    intro hEq
    rw [hEq] at hOneRe
    norm_num at hOneRe
  choose c hc hPole using
    nicolasPsiMellinTailContinuation_three_simplePoleLimit_Ioi
      hZero hRhoZero hRhoOne
  let D : Set (Prod Real Real) :=
    {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)}
  let l : Filter (Prod Real Real) :=
    nhdsWithin ((0 : Real), (0 : Real)) D
  let u : Prod Real Real -> Real := fun p => p.2 - p.1
  let z : Prod Real Real -> Complex := fun p =>
    nicolasRightmostRayPoint rho p.1
  let z0 : Complex := 1 - rho
  have hFst : Tendsto (fun p : Prod Real Real => p.1) l (nhds 0) := by
    exact continuousAt_fst.tendsto.mono_left nhdsWithin_le_nhds
  have hSnd : Tendsto (fun p : Prod Real Real => p.2) l (nhds 0) := by
    exact continuousAt_snd.tendsto.mono_left nhdsWithin_le_nhds
  have hU : Tendsto u l (nhds 0) := by
    dsimp [u]
    simpa using hSnd.sub hFst
  have hSndPos : Filter.Eventually
      (fun p : Prod Real Real => 0 < p.2) l := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.1.trans hp.2
  have hUPos : Filter.Eventually (fun p : Prod Real Real => 0 < u p) l := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    dsimp [u]
    linarith [hp.2]
  have hSndWithin : Tendsto (fun p : Prod Real Real => p.2) l
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro hSnd hSndPos
  have hUWithin : Tendsto u l (nhdsWithin 0 (Ioi (0 : Real))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro hU hUPos
  have hPoleComp : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) *
        nicolasPsiMellinTailContinuation 3 (rho + (p.2 : Complex)))
      l (nhds c) := hPole.comp hSndWithin
  have hBaseArg : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex))) l
      (nhdsWithin 1 (Set.compl {(1 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    . have hCast : Tendsto (fun p : Prod Real Real => (u p : Complex))
          l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hU
      simpa using hCast.add tendsto_const_nhds
    . filter_upwards [hUPos] with p hp
      apply Set.mem_compl_singleton_iff.mpr
      intro hEq
      have hRe := congrArg Complex.re hEq
      simp only [Complex.ofReal_re, Complex.one_re] at hRe
      linarith
  have hBaseTail : Tendsto (fun p : Prod Real Real =>
      nicolasPsiMellinTailContinuation 3
        (((u p + 1 : Real) : Complex))) l
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1) -
        nicolasPsiMellinStartup 3 1)) :=
    nicolasPsiMellinTailContinuation_three_tendsto_one.comp hBaseArg
  have hSndCast : Tendsto (fun p : Prod Real Real => (p.2 : Complex))
      l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hSnd
  have hScaledBase : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) * nicolasPsiMellinTailContinuation 3
        (((u p + 1 : Real) : Complex))) l (nhds 0) := by
    simpa using hSndCast.mul hBaseTail
  have hZ : Tendsto z l (nhds z0) := by
    have hFstCast : Tendsto (fun p : Prod Real Real => (p.1 : Complex))
        l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hFst
    dsimp [z, z0, nicolasRightmostRayPoint]
    simpa using (tendsto_const_nhds.sub hFstCast)
  have hz0Ne : Not (z0 = 0) := by
    dsimp [z0]
    exact sub_ne_zero.mpr (Ne.symm hRhoOne)
  have hNumerator : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex))) l (nhds 1) := by
    have hCast : Tendsto (fun p : Prod Real Real => (u p : Complex))
        l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hU
    simpa using hCast.add tendsto_const_nhds
  have hPrefactor : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex)) / z p) l (nhds (1 / z0)) :=
    hNumerator.div hZ hz0Ne
  have hPowerAt : Tendsto (fun p : Prod Real Real =>
      (3 : Complex) ^ (z p)) l (nhds ((3 : Complex) ^ z0)) := by
    have hContinuous : ContinuousAt (fun w : Complex =>
        (3 : Complex) ^ w) z0 := by
      fun_prop
    exact hContinuous.tendsto.comp hZ
  have hDifference : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) *
          nicolasPsiMellinTailContinuation 3 (rho + (p.2 : Complex)) -
        (3 : Complex) ^ (z p) *
          ((p.2 : Complex) * nicolasPsiMellinTailContinuation 3
            (((u p + 1 : Real) : Complex)))) l (nhds c) := by
    simpa using hPoleComp.sub (hPowerAt.mul hScaledBase)
  let d : Complex := c / z0
  have hd : Not (d = 0) := div_ne_zero hc hz0Ne
  refine Exists.intro d (And.intro hd ?_)
  have hProduct := hPrefactor.mul hDifference
  convert hProduct using 1
  . funext p
    have hShift :
        ((((p.2 - p.1 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1)) =
          rho + (p.2 : Complex) := by
      unfold nicolasRightmostRayPoint
      push_cast
      ring
    unfold nicolasJRightmostRayTranslatedScaledKernel
      nicolasJMellinShiftIntegrand
    rw [hShift]
    dsimp [u, z, nicolasRightmostRayPoint]
    ring
  . dsimp [d]
    ring

theorem exists_nicolasRightmostRayScaledKernel_uniform
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps v : Real, 0 < eps -> eps < v -> v <= r ->
            norm (nicolasJRightmostRayTranslatedScaledKernel rho eps v - d) <=
              norm d / 4))) := by
  choose d hd hLimit using
    nicolasJRightmostRayTranslatedScaledKernel_tendsto hZero hHalf hOneRe
  have hdNorm : 0 < norm d := norm_pos_iff.mpr hd
  have hClose : Filter.Eventually
      (fun p : Prod Real Real =>
        norm (nicolasJRightmostRayTranslatedScaledKernel rho p.1 p.2 - d) <
          norm d / 4)
      (nhdsWithin ((0 : Real), (0 : Real))
        {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)}) := by
    have hBall := hLimit.eventually
      (Metric.ball_mem_nhds d (by positivity : 0 < norm d / 4))
    simpa [Metric.mem_ball, dist_eq_norm] using hBall
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hClose
  choose eta hEta hCloseEta using hClose
  let r : Real := min (eta / 2) (1 / 4)
  have hrPos : 0 < r := by
    dsimp [r]
    exact lt_min (by positivity) (by norm_num)
  have hrHalf : r < 1 / 2 := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrEta : r < eta := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps v hEps hEpsV hVr
  have hVPos : 0 < v := hEps.trans hEpsV
  have hDist : dist (eps, v) ((0 : Real), (0 : Real)) < eta := by
    change max (dist eps 0) (dist v 0) < eta
    rw [max_lt_iff]
    constructor
    . rw [Real.dist_eq, sub_zero, abs_of_pos hEps]
      exact hEpsV.trans_le hVr |>.trans hrEta
    . rw [Real.dist_eq, sub_zero, abs_of_pos hVPos]
      exact hVr.trans_lt hrEta
  exact (hCloseEta hDist (And.intro hEps hEpsV)).le

theorem nicolasJRightmostRayTranslatedScaledKernelFilled_intervalIntegrable
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps r : Real} (hEps : 0 < eps) (hEpsR : eps < r)
    (hWidth : r - eps <= 1) :
    IntervalIntegrable
      (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps)
      volume eps r := by
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hzZero : Not (nicolasRightmostRayPoint rho eps = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    unfold nicolasRightmostRayPoint at hEqIm
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.zero_im] at hEqIm
    apply hIm
    linarith
  apply ContinuousOn.intervalIntegrable
  intro v hv
  have hvIcc : Membership.mem (Icc eps r) v := by
    simpa [uIcc, min_eq_left hEpsR.le, max_eq_right hEpsR.le] using hv
  have hU : 0 <= v - eps := by linarith [hvIcc.1]
  have hULe : v - eps <= 1 := by linarith [hvIcc.2]
  let s : Complex := rho + (v : Complex)
  have hsIm : s.im = rho.im := by
    dsimp [s]
    simp
  have hsZero : Not (s = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.zero_im] at hEqIm
    exact hIm hEqIm
  have hsOne : Not (s = 1) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.one_im] at hEqIm
    exact hIm hEqIm
  have hVPos : 0 < v := hEps.trans_le hvIcc.1
  have hZeta : Not (riemannZeta s = 0) := by
    dsimp [s]
    exact hRay v hVPos
  have hFactor : Not (nicolasZetaPoleFactor s = 0) :=
    nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
  have hShift :
      ((((v - eps + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps)) = s := by
    dsimp [s, nicolasRightmostRayPoint]
    push_cast
    ring
  have hShiftZero : Not
      ((((v - eps + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps) = 0) := by
    rw [hShift]
    exact hsZero
  have hShiftFactor : Not
      (nicolasZetaPoleFactor
        (((v - eps + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps) = 0) := by
    rw [hShift]
    exact hFactor
  have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
    (u := v - eps) (z := nicolasRightmostRayPoint rho eps)
    hU hzZero hShiftZero hShiftFactor
  have hEmbed : ContinuousAt (fun w : Real =>
      (w - eps, nicolasRightmostRayPoint rho eps)) v := by
    fun_prop
  have hTail : ContinuousAt (fun w : Real =>
      nicolasJMellinShiftIntegrandFilled
        (nicolasRightmostRayPoint rho eps) (w - eps)) v := by
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    simpa [Function.comp_def] using hComp
  have hCast : ContinuousAt (fun w : Real => (w : Complex)) v := by
    fun_prop
  unfold nicolasJRightmostRayTranslatedScaledKernelFilled
  exact (hCast.mul hTail).continuousWithinAt

theorem exists_nicolasRightmostRayScaledKernelFilled_uniform
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps v : Real, 0 < eps -> eps < v -> v <= r ->
            norm
              (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v - d) <=
              norm d / 4))) := by
  choose d r hd hrPos hrHalf hUniform using
    exists_nicolasRightmostRayScaledKernel_uniform hZero hHalf hOneRe
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps v hEps hEpsV hVr
  rw [nicolasJRightmostRayTranslatedScaledKernelFilled_eq_raw
    hZero hHalf hOneRe hRay hEps hEpsV]
  exact hUniform eps v hEps hEpsV hVr

end

end Robin1984
