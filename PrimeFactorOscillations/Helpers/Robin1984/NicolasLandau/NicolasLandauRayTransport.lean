/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauRightmostRay.lean
Original source lines 27-355. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauComplexFrontier

/-!
# Complex Mellin transport for the positive tail

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem norm_intervalIntegral_inv_smul_sub_le_of_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [CompleteSpace E]
    {f : Real -> E} {a b delta : Real} {V : E}
    (hf : IntervalIntegrable f volume a b) (ha : 0 < a) (hb : 0 < b)
    (hDelta : 0 <= delta)
    (hBound : forall x : Real, Membership.mem (uIoc a b) x ->
      norm (f x - V) <= delta) :
    norm (intervalIntegral
        (fun x : Real => HSMul.hSMul (Inv.inv x) (f x)) a b volume -
      HSMul.hSMul (Real.log (b / a)) V) <=
      delta * abs (Real.log (b / a)) := by
  have hSubset : uIcc a b <= Ioi (0 : Real) := by
    simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hInv : ContinuousOn (fun x : Real => Inv.inv x) (uIcc a b) := by
    intro x hx
    exact (NormedField.continuousAt_inv.mpr
      (ne_of_gt (hSubset hx))).continuousWithinAt
  have hWeighted : IntervalIntegrable
      (fun x : Real => HSMul.hSMul (Inv.inv x) (f x)) volume a b :=
    hf.continuousOn_smul hInv
  have hConst : IntervalIntegrable
      (fun x : Real => HSMul.hSMul (Inv.inv x) V) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact hInv.smul continuousOn_const
  have hReal : IntervalIntegrable
      (fun x : Real => Inv.inv x * delta) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact hInv.mul continuousOn_const
  calc
    norm (intervalIntegral
          (fun x : Real => HSMul.hSMul (Inv.inv x) (f x)) a b volume -
        HSMul.hSMul (Real.log (b / a)) V) =
        norm (intervalIntegral
          (fun x : Real => HSMul.hSMul (Inv.inv x) (f x - V))
          a b volume) := by
      congr 1
      have hConstIntegral : HSMul.hSMul (Real.log (b / a)) V =
          intervalIntegral
            (fun x : Real => HSMul.hSMul (Inv.inv x) V) a b volume := by
        rw [intervalIntegral.integral_smul_const,
          integral_inv_of_pos ha hb]
      rw [hConstIntegral, <- intervalIntegral.integral_sub hWeighted hConst]
      congr 1
      funext x
      exact (smul_sub _ _ _).symm
    _ <= abs (intervalIntegral
        (fun x : Real => Inv.inv x * delta) a b volume) := by
      apply intervalIntegral.norm_integral_le_abs_of_norm_le
      . filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
        have hxPos : 0 < x :=
          lt_of_lt_of_le (lt_min ha hb) (uIoc_subset_uIcc hx).1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxPos)]
        exact mul_le_mul_of_nonneg_left (hBound x hx)
          (inv_nonneg.mpr hxPos.le)
      . exact hReal
    _ = delta * abs (Real.log (b / a)) := by
      simp_rw [mul_comm]
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
      rw [abs_mul, abs_of_nonneg hDelta]

def nicolasLandauRpowComplexContinuation
    (X b : Real) (z : Complex) : Complex :=
  (X : Complex) ^ (z - (b : Complex)) / ((b : Complex) - z)

def nicolasLandauPositiveComplexContinuationFilled
    (X b : Real) (z : Complex) : Complex :=
  nicolasJShiftedComplexContinuationFilled z -
    nicolasJComplexMellinStartup X z +
      nicolasLandauRpowComplexContinuation X b z

def nicolasLandauPositiveComplexMellin
    (X b : Real) (z : Complex) : Complex :=
  integral (volume.restrict (Ioi X)) (fun x : Real =>
    (x : Complex) ^ (z - 1) *
      (nicolasLandauPositiveTail b x : Complex))

theorem complexMGF_log_nicolasLandauPositiveMeasure_eq_complexMellin
    {X b : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x) {z : Complex} :
    complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b) z =
      nicolasLandauPositiveComplexMellin X b z := by
  have hDensity := nicolasLandauPositiveDensity_aemeasurable
    (X := X) (b := b) hX
  let measurableDensity : Real -> ENNReal :=
    hDensity.mk (nicolasLandauPositiveDensity b)
  have hDensityEq : Filter.Eventually
      (fun x : Real => nicolasLandauPositiveDensity b x =
        measurableDensity x)
      (ae (volume.restrict (Ioi X))) := hDensity.ae_eq_mk
  have hDensityTop : Filter.Eventually
      (fun x : Real => measurableDensity x < Top.top)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [hDensityEq] with x hx
    rw [<- hx]
    exact ENNReal.ofReal_lt_top
  have hMeasureEq :
      (volume.restrict (Ioi X)).withDensity
          (nicolasLandauPositiveDensity b) =
        (volume.restrict (Ioi X)).withDensity measurableDensity :=
    withDensity_congr_ae hDensityEq
  unfold complexMGF nicolasLandauPositiveMeasure
  rw [hMeasureEq, integral_withDensity_eq_integral_toReal_smul
    hDensity.measurable_mk hDensityTop]
  unfold nicolasLandauPositiveComplexMellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hxNe : Not ((x : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hxPos.ne'
  have hTail : 0 <= nicolasLandauPositiveTail b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      nicolasLandauPositiveTail b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  have hExp : Complex.exp (z * (Real.log x : Complex)) =
      (x : Complex) ^ z := by
    rw [Complex.cpow_def_of_ne_zero hxNe, <- Complex.ofReal_log hxPos.le]
    congr 1
    ring
  change SMul.smul (measurableDensity x).toReal
      (Complex.exp (z * (Real.log x : Complex))) =
    (x : Complex) ^ (z - 1) *
      (nicolasLandauPositiveTail b x : Complex)
  rw [<- hdx]
  unfold nicolasLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  change ((x ^ (-1 : Real) * nicolasLandauPositiveTail b x : Real) : Complex) *
      Complex.exp (z * (Real.log x : Complex)) =
    (x : Complex) ^ (z - 1) *
      (nicolasLandauPositiveTail b x : Complex)
  rw [hExp]
  push_cast
  calc
    ((x ^ (-1 : Real) : Real) : Complex) *
          (nicolasLandauPositiveTail b x : Complex) * (x : Complex) ^ z =
        (((x ^ (-1 : Real) : Real) : Complex) * (x : Complex) ^ z) *
          (nicolasLandauPositiveTail b x : Complex) := by ring
    _ = ((x : Complex) ^ ((-1 : Real) : Complex) *
          (x : Complex) ^ z) *
          (nicolasLandauPositiveTail b x : Complex) := by
      rw [Complex.ofReal_cpow hxPos.le]
    _ = (x : Complex) ^ (((-1 : Real) : Complex) + z) *
          (nicolasLandauPositiveTail b x : Complex) := by
      rw [Complex.cpow_add _ _ hxNe]
    _ = (x : Complex) ^ (z - 1) *
          (nicolasLandauPositiveTail b x : Complex) := by
      congr 2
      norm_num [sub_eq_add_neg, add_comm]

theorem nicolasLandauRpowComplexTailMellin_eq_continuation
    {X b : Real} (hX : 0 < X) {z : Complex} (hz : z.re < b) :
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) =
      nicolasLandauRpowComplexContinuation X b z := by
  have hExponent : (z - (b : Complex) - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith
  calc
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) =
        integral (volume.restrict (Ioi X)) (fun x : Real =>
          (x : Complex) ^ (z - (b : Complex) - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxPos : 0 < x := hX.trans hx
      have hxNe : Not ((x : Complex) = 0) :=
        Complex.ofReal_ne_zero.mpr hxPos.ne'
      change (x : Complex) ^ (z - 1) *
          ((x ^ (-b) : Real) : Complex) =
        (x : Complex) ^ (z - (b : Complex) - 1)
      rw [Complex.ofReal_cpow hxPos.le]
      rw [<- Complex.cpow_add _ _ hxNe]
      congr 1
      push_cast
      ring
    _ = -(X : Complex) ^ (z - (b : Complex) - 1 + 1) /
          (z - (b : Complex) - 1 + 1) :=
      integral_Ioi_cpow_of_lt hExponent hX
    _ = nicolasLandauRpowComplexContinuation X b z := by
      unfold nicolasLandauRpowComplexContinuation
      have hDen : Not (z - (b : Complex) = 0) := by
        intro hEq
        have hRe := congrArg Complex.re hEq
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hRe
        linarith
      have hDen' : Not ((b : Complex) - z = 0) := by
        exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hDen))
      field_simp [hDen, hDen']
      ring

theorem nicolasLandauRpowComplexContinuation_analyticAt
    {X b : Real} (hX : 0 < X) {z : Complex}
    (hz : Not (z = (b : Complex))) :
    AnalyticAt Complex (nicolasLandauRpowComplexContinuation X b) z := by
  have hXNe : Not ((X : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hX.ne'
  have hNumerator : AnalyticAt Complex (fun w : Complex =>
      (X : Complex) ^ (w - (b : Complex))) z := by
    have hDiff : Differentiable Complex (fun w : Complex =>
        (X : Complex) ^ (w - (b : Complex))) := by
      intro w
      exact (differentiableAt_id.sub_const (b : Complex)).const_cpow
        (Or.inl hXNe)
    exact hDiff.analyticAt z
  have hDenominator : AnalyticAt Complex
      (fun w : Complex => (b : Complex) - w) z := by
    fun_prop
  unfold nicolasLandauRpowComplexContinuation
  exact hNumerator.div hDenominator (sub_ne_zero.mpr (Ne.symm hz))

theorem nicolasJ_complexMellin_integrableOn_Ioi_three
    {z : Complex} (hz : z.re < 0) :
    IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex))
      (Ioi (3 : Real)) := by
  have hTriple := nicolasJMellinTriple_integrable hz
  have hOuter := hTriple.integral_prod_left
  apply hOuter.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact nicolasJMellinTriple_inner_eq hx.le

theorem nicolasJShiftedComplexContinuationFilled_eq_mellin_of_re_neg
    {z : Complex} (hz : z.re < 0) :
    nicolasJShiftedComplexContinuationFilled z = nicolasJMellin z := by
  unfold nicolasJShiftedComplexContinuationFilled
  calc
    integral (volume.restrict (Ioi (0 : Real)))
        (nicolasJMellinShiftIntegrandFilled z) =
        integral (volume.restrict (Ioi (0 : Real)))
          (nicolasJMellinShiftIntegrand z) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact nicolasJMellinShiftIntegrandFilled_eq_raw hz hu
    _ = nicolasJMellin z :=
      (nicolasJMellin_eq_integral_shift hz).symm

theorem nicolasJMellin_eq_startup_add_tail_of_re_neg
    {X : Real} (hX : 3 <= X) {z : Complex} (hz : z.re < 0) :
    nicolasJMellin z = nicolasJComplexMellinStartup X z +
      integral (volume.restrict (Ioi X)) (fun x : Real =>
        (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) := by
  have hJThree := nicolasJ_complexMellin_integrableOn_Ioi_three hz
  have hJX : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hJStartup : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) (Ioc 3 X) :=
    hJThree.mono_set Ioc_subset_Ioi_self
  unfold nicolasJMellin nicolasJComplexMellinStartup
  rw [<- Ioc_union_Ioi_eq_Ioi hX,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hJStartup
  . exact hJX

theorem nicolasLandauRpowComplexTailMellin_integrableOn
    {X b : Real} (hX : 0 < X) {z : Complex} (hz : z.re < b) :
    IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex))
      (Ioi X) := by
  have hExponent : (z - (b : Complex) - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hBase := integrableOn_Ioi_cpow_of_lt hExponent hX
  apply hBase.congr_fun
  . intro x hx
    have hxPos : 0 < x := hX.trans hx
    have hxNe : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr hxPos.ne'
    change (x : Complex) ^ (z - (b : Complex) - 1) =
      (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)
    rw [Complex.ofReal_cpow hxPos.le]
    rw [<- Complex.cpow_add _ _ hxNe]
    congr 1
    push_cast
    ring
  . exact measurableSet_Ioi

theorem nicolasLandauPositiveComplexMellin_eq_continuation_of_re_neg
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    {z : Complex} (hz : z.re < 0) :
    nicolasLandauPositiveComplexMellin X b z =
      nicolasLandauPositiveComplexContinuationFilled X b z := by
  have hJThree := nicolasJ_complexMellin_integrableOn_Ioi_three hz
  have hJX : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hzB : z.re < b := lt_trans hz hb
  have hRpow := nicolasLandauRpowComplexTailMellin_integrableOn
    hXPos hzB
  have hDecomp : (fun x : Real =>
      (x : Complex) ^ (z - 1) *
        (nicolasLandauPositiveTail b x : Complex)) =
      (fun x : Real =>
        (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) +
      (fun x : Real =>
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) := by
    funext x
    unfold nicolasLandauPositiveTail
    push_cast
    simp only [Pi.add_apply]
    ring
  unfold nicolasLandauPositiveComplexMellin
    nicolasLandauPositiveComplexContinuationFilled
  rw [hDecomp]
  change integral (volume.restrict (Ioi X)) (fun x : Real =>
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex) +
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) = _
  rw [integral_add hJX hRpow]
  rw [nicolasLandauRpowComplexTailMellin_eq_continuation hXPos hzB]
  have hSplit := nicolasJMellin_eq_startup_add_tail_of_re_neg hX hz
  rw [<- nicolasJShiftedComplexContinuationFilled_eq_mellin_of_re_neg hz] at hSplit
  rw [hSplit]
  ring

theorem nicolasLandauComplexMGF_eq_continuationFilled_of_re_neg
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    {z : Complex} (hz : z.re < 0) :
    complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b) z =
      nicolasLandauPositiveComplexContinuationFilled X b z := by
  rw [complexMGF_log_nicolasLandauPositiveMeasure_eq_complexMellin hX hPos]
  exact nicolasLandauPositiveComplexMellin_eq_continuation_of_re_neg
    hX hb hz

end

end Robin1984
