/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauCompactBlock.lean
Original source lines 26-344. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPositiveTail

/-!
# The compact-parameter kernel and its uniform bound

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

def nicolasFilledOneRadius : Real :=
  Classical.choose
    exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one

theorem nicolasFilledOneRadius_pos : 0 < nicolasFilledOneRadius :=
  (Classical.choose_spec
    exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one).1

theorem nicolasFilledOneRadius_analytic
    {s : Complex}
    (hs : Membership.mem
      (Metric.ball (1 : Complex) nicolasFilledOneRadius) s) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled s :=
  (Classical.choose_spec
    exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one).2 s hs

def nicolasCompactZRadius : Real :=
  min (nicolasFilledOneRadius / 16) (1 / 64)

theorem nicolasCompactZRadius_pos : 0 < nicolasCompactZRadius := by
  unfold nicolasCompactZRadius
  exact lt_min (div_pos nicolasFilledOneRadius_pos (by norm_num))
    (by norm_num)

theorem nicolasCompactZRadius_le_oneRadius_div_sixteen :
    nicolasCompactZRadius <= nicolasFilledOneRadius / 16 := by
  unfold nicolasCompactZRadius
  exact min_le_left _ _

theorem nicolasCompactZRadius_le_one_sixty_four :
    nicolasCompactZRadius <= 1 / 64 := by
  unfold nicolasCompactZRadius
  exact min_le_right _ _

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_compact_base
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled
      (((u + 1 : Real) : Complex)) := by
  by_cases huZero : u = 0
  case pos =>
    subst u
    simpa using nicolasPsiMellinTailContinuationFilled_analyticAt_one
  case neg =>
    apply nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re
    simp only [Complex.ofReal_re]
    have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm huZero)
    linarith

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_compact_shift
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : norm z < 4 * nicolasCompactZRadius) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled
      (((u + 1 : Real) : Complex) - z) := by
  have hRadius := nicolasFilledOneRadius_pos
  have hFourRadius :
      4 * nicolasCompactZRadius <= nicolasFilledOneRadius / 4 := by
    calc
      4 * nicolasCompactZRadius <=
          4 * (nicolasFilledOneRadius / 16) :=
        mul_le_mul_of_nonneg_left
          nicolasCompactZRadius_le_oneRadius_div_sixteen (by norm_num)
      _ = nicolasFilledOneRadius / 4 := by ring
  have hzRadius : norm z < nicolasFilledOneRadius / 4 :=
    hz.trans_le hFourRadius
  by_cases huSmall : u < nicolasFilledOneRadius / 2
  case pos =>
    apply nicolasFilledOneRadius_analytic
    rw [Metric.mem_ball, dist_eq_norm]
    have hDifference :
        (((u + 1 : Real) : Complex) - z) - (1 : Complex) =
          (u : Complex) - z := by
      push_cast
      ring
    rw [hDifference]
    calc
      norm ((u : Complex) - z) <= norm (u : Complex) + norm z :=
        norm_sub_le _ _
      _ = u + norm z := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
      _ < nicolasFilledOneRadius / 2 +
          nicolasFilledOneRadius / 4 := add_lt_add huSmall hzRadius
      _ < nicolasFilledOneRadius := by linarith
  case neg =>
    apply nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re
    have hzRe : z.re <= norm z := Complex.re_le_norm z
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith

theorem nicolasJShiftNumeratorFilled_analyticAt_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : norm z < 4 * nicolasCompactZRadius) :
    AnalyticAt Complex (nicolasJShiftNumeratorFilled u) z := by
  let s : Complex := ((u + 1 : Real) : Complex)
  have hTailShift : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled (s - z) := by
    dsimp [s]
    exact nicolasPsiMellinTailContinuationFilled_analyticAt_compact_shift
      hu hz
  have hAffine : AnalyticAt Complex (fun w : Complex => s - w) z :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s - w)) z := by
    have hComp := hTailShift.comp_of_eq hAffine rfl
    apply hComp.congr
    exact Eventually.of_forall (fun _ => rfl)
  have hPowerDifferentiable : Differentiable Complex
      (fun w : Complex => (3 : Complex) ^ w) := by
    intro w
    exact DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (by norm_num))
  have hPower : AnalyticAt Complex
      (fun w : Complex => (3 : Complex) ^ w) z :=
    hPowerDifferentiable.analyticAt z
  have hTailBase : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s := by
    dsimp [s]
    exact nicolasPsiMellinTailContinuationFilled_analyticAt_compact_base hu
  have hTailConst : AnalyticAt Complex (fun _ : Complex =>
      nicolasPsiMellinTailContinuationFilled s) z := analyticAt_const
  unfold nicolasJShiftNumeratorFilled
  change AnalyticAt Complex (fun w : Complex =>
    nicolasPsiMellinTailContinuationFilled (s - w) -
      (3 : Complex) ^ w * nicolasPsiMellinTailContinuationFilled s) z
  exact hShift.sub (hPower.mul hTailConst)

def nicolasCompactNumeratorDomain : Set (Prod Real Complex) :=
  Set.prod (Icc (0 : Real) 1)
    (Metric.closedBall (0 : Complex) (3 * nicolasCompactZRadius))

theorem nicolasJShiftNumeratorFilled_continuousOn_compact :
    ContinuousOn (fun p : Prod Real Complex =>
      nicolasJShiftNumeratorFilled p.1 p.2)
      nicolasCompactNumeratorDomain := by
  intro p hp
  have hu : Membership.mem (Icc (0 : Real) 1) p.1 := hp.1
  have hzClosed : Membership.mem
      (Metric.closedBall (0 : Complex) (3 * nicolasCompactZRadius)) p.2 :=
    hp.2
  have hzNorm : norm p.2 <= 3 * nicolasCompactZRadius := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hzClosed
  have hzStrict : norm p.2 < 4 * nicolasCompactZRadius := by
    have hRadius := nicolasCompactZRadius_pos
    linarith
  let s0 : Prod Real Complex -> Complex := fun q =>
    (((q.1 + 1 : Real) : Complex))
  let s1 : Prod Real Complex -> Complex := fun q => s0 q - q.2
  have hs0Continuous : ContinuousAt s0 p := by
    dsimp [s0]
    fun_prop
  have hs1Continuous : ContinuousAt s1 p := by
    dsimp [s1]
    exact hs0Continuous.sub continuousAt_snd
  have hTailBase : ContinuousAt
      (fun q : Prod Real Complex =>
        nicolasPsiMellinTailContinuationFilled (s0 q)) p := by
    exact
      (nicolasPsiMellinTailContinuationFilled_analyticAt_compact_base hu).continuousAt.comp_of_eq
        hs0Continuous rfl
  have hTailShift : ContinuousAt
      (fun q : Prod Real Complex =>
        nicolasPsiMellinTailContinuationFilled (s1 q)) p := by
    exact
      (nicolasPsiMellinTailContinuationFilled_analyticAt_compact_shift
        hu hzStrict).continuousAt.comp_of_eq hs1Continuous rfl
  have hPower : ContinuousAt
      (fun q : Prod Real Complex => (3 : Complex) ^ q.2) p := by
    exact continuousAt_snd.const_cpow (Or.inl (by norm_num))
  unfold nicolasJShiftNumeratorFilled
  change ContinuousWithinAt (fun q : Prod Real Complex =>
    nicolasPsiMellinTailContinuationFilled (s1 q) -
      (3 : Complex) ^ q.2 *
        nicolasPsiMellinTailContinuationFilled (s0 q))
    nicolasCompactNumeratorDomain p
  exact (hTailShift.sub (hPower.mul hTailBase)).continuousWithinAt

theorem nicolasCompactNumeratorDomain_isCompact :
    IsCompact nicolasCompactNumeratorDomain := by
  unfold nicolasCompactNumeratorDomain
  exact isCompact_Icc.prod (isCompact_closedBall _ _)

theorem exists_nicolasCompactNumeratorBound :
    Exists fun C : Real =>
      forall u : Real,
        Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem
            (Metric.closedBall (0 : Complex)
              (3 * nicolasCompactZRadius)) z ->
          norm (nicolasJShiftNumeratorFilled u z) <= C := by
  let f : Prod Real Complex -> Real := fun p =>
    norm (nicolasJShiftNumeratorFilled p.1 p.2)
  have hf : ContinuousOn f nicolasCompactNumeratorDomain := by
    dsimp [f]
    exact nicolasJShiftNumeratorFilled_continuousOn_compact.norm
  have hBound : BddAbove (f '' nicolasCompactNumeratorDomain) :=
    nicolasCompactNumeratorDomain_isCompact.bddAbove_image
      hf
  choose C hC using hBound
  refine Exists.intro C ?_
  intro u hu z hz
  have hMember : Membership.mem (f '' nicolasCompactNumeratorDomain)
      (f (u, z)) := by
    apply mem_image_of_mem
    change And
      (Membership.mem (Icc (0 : Real) 1) u)
      (Membership.mem
        (Metric.closedBall (0 : Complex) (3 * nicolasCompactZRadius)) z)
    exact And.intro hu hz
  have hValue := hC hMember
  dsimp [f] at hValue
  exact hValue

def nicolasCompactNumeratorBound : Real :=
  max (Classical.choose exists_nicolasCompactNumeratorBound) 0

theorem nicolasCompactNumeratorBound_nonneg :
    0 <= nicolasCompactNumeratorBound := by
  unfold nicolasCompactNumeratorBound
  exact le_max_right _ _

theorem norm_nicolasJShiftNumeratorFilled_le_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z) :
    norm (nicolasJShiftNumeratorFilled u z) <=
      nicolasCompactNumeratorBound := by
  have hChosen :=
    (Classical.choose_spec exists_nicolasCompactNumeratorBound) u hu z hz
  exact hChosen.trans (le_max_left _ _)

theorem nicolasJShiftNumeratorFilled_differentiableOn_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u) :
    DifferentiableOn Complex (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) := by
  intro z hz
  have hzNorm : norm z < 3 * nicolasCompactZRadius := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzFour : norm z < 4 * nicolasCompactZRadius := by
    have hRadius := nicolasCompactZRadius_pos
    linarith
  exact
    (nicolasJShiftNumeratorFilled_analyticAt_compact hu hzFour).differentiableAt.differentiableWithinAt

theorem norm_nicolasJMellinShiftIntegrandFilled_le_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) z) :
    norm (nicolasJMellinShiftIntegrandFilled z u) <=
      2 * (nicolasCompactNumeratorBound /
        (3 * nicolasCompactZRadius)) := by
  let R : Real := 3 * nicolasCompactZRadius
  let M : Real := nicolasCompactNumeratorBound
  have hRPos : 0 < R := by
    dsimp [R]
    exact mul_pos (by norm_num) nicolasCompactZRadius_pos
  have hMNonneg : 0 <= M := by
    dsimp [M]
    exact nicolasCompactNumeratorBound_nonneg
  have hMaps : MapsTo (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) R)
      (Metric.closedBall (nicolasJShiftNumeratorFilled u 0) M) := by
    intro w hw
    rw [nicolasJShiftNumeratorFilled_zero]
    rw [Metric.mem_closedBall, dist_zero_right]
    apply norm_nicolasJShiftNumeratorFilled_le_compact hu
    exact Metric.ball_subset_closedBall hw
  have hDslope := Complex.norm_dslope_le_div_of_mapsTo_ball
    (nicolasJShiftNumeratorFilled_differentiableOn_compact hu)
    hMaps hz
  have huOnePos : 0 < u + 1 := by linarith [hu.1]
  have huOneLe : u + 1 <= 2 := by linarith [hu.2]
  have hQuotientNonneg : 0 <= M / R := div_nonneg hMNonneg hRPos.le
  unfold nicolasJMellinShiftIntegrandFilled
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huOnePos]
  calc
    (u + 1) * norm (dslope (nicolasJShiftNumeratorFilled u) 0 z) <=
        (u + 1) * (M / R) :=
      mul_le_mul_of_nonneg_left hDslope huOnePos.le
    _ <= 2 * (M / R) :=
      mul_le_mul_of_nonneg_right huOneLe hQuotientNonneg
    _ = 2 * (nicolasCompactNumeratorBound /
        (3 * nicolasCompactZRadius)) := by
      dsimp [M, R]

def nicolasCompactIntegrandBound : Real :=
  2 * (nicolasCompactNumeratorBound /
    (3 * nicolasCompactZRadius))


theorem nicolasJMellinShiftIntegrandFilled_differentiableOn_compact
    {u : Real} (hu : Membership.mem (Ioc (0 : Real) 1) u) :
    DifferentiableOn Complex
      (fun z : Complex => nicolasJMellinShiftIntegrandFilled z u)
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) := by
  have huClosed : Membership.mem (Icc (0 : Real) 1) u :=
    And.intro hu.1.le hu.2
  intro z hz
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      hu.1).differentiableAt.differentiableWithinAt
  case neg =>
    have hNumeratorAt : DifferentiableAt Complex
        (nicolasJShiftNumeratorFilled u) z :=
      (nicolasJShiftNumeratorFilled_differentiableOn_compact
        huClosed z hz).differentiableAt
          (Metric.isOpen_ball.mem_nhds hz)
    have hDslopeAt : DifferentiableAt Complex
        (dslope (nicolasJShiftNumeratorFilled u) 0) z :=
      (differentiableAt_dslope_of_ne hzZero).2 hNumeratorAt
    unfold nicolasJMellinShiftIntegrandFilled
    exact (analyticAt_const.differentiableAt.mul hDslopeAt).differentiableWithinAt

end

end Robin1984

