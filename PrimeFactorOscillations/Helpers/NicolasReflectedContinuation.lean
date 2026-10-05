/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasReflectedMeasure

/-!
# Analytic continuation for the reflected Nicolas tail

Identifies the reflected measure transform with its continuation and
applies the checked Landau principle to eventual nonnegativity.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter MeasureTheory ProbabilityTheory Set Robin1984
open scoped ENNReal Topology

noncomputable section

def nicolasReflectedComplexMellin (X A b : Real) (z : Complex) : Complex :=
  integral (volume.restrict (Ioi X)) (fun x : Real =>
    (x : Complex) ^ (z - 1) * (nicolasReflectedTail A b x : Complex))

def nicolasReflectedComplexContinuation (X A b : Real) (z : Complex) : Complex :=
  ((A + 1 : Real) : Complex) * nicolasLandauRpowComplexContinuation X b z -
    nicolasLandauPositiveComplexContinuationFilled X b z

theorem complexMGF_log_nicolasReflectedMeasure_eq_complexMellin
    {X A b : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasReflectedTail A b x) {z : Complex} :
    complexMGF (fun x : Real => Real.log x)
        (nicolasReflectedMeasure X A b) z =
      nicolasReflectedComplexMellin X A b z := by
  have hDensity := nicolasReflectedDensity_aemeasurable
    (X := X) (A := A) (b := b) hX
  let measurableDensity : Real -> ENNReal :=
    hDensity.mk (nicolasReflectedDensity A b)
  have hDensityEq : Filter.Eventually
      (fun x : Real => nicolasReflectedDensity A b x =
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
          (nicolasReflectedDensity A b) =
        (volume.restrict (Ioi X)).withDensity measurableDensity :=
    withDensity_congr_ae hDensityEq
  unfold complexMGF nicolasReflectedMeasure
  rw [hMeasureEq, integral_withDensity_eq_integral_toReal_smul
    hDensity.measurable_mk hDensityTop]
  unfold nicolasReflectedComplexMellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hxNe : Not ((x : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hxPos.ne'
  have hTail : 0 <= nicolasReflectedTail A b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      nicolasReflectedTail A b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  have hExp : Complex.exp (z * (Real.log x : Complex)) =
      (x : Complex) ^ z := by
    rw [Complex.cpow_def_of_ne_zero hxNe, <- Complex.ofReal_log hxPos.le]
    congr 1
    ring
  change SMul.smul (measurableDensity x).toReal
      (Complex.exp (z * (Real.log x : Complex))) =
    (x : Complex) ^ (z - 1) *
      (nicolasReflectedTail A b x : Complex)
  rw [<- hdx]
  unfold nicolasReflectedDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  change ((x ^ (-1 : Real) * nicolasReflectedTail A b x : Real) : Complex) *
      Complex.exp (z * (Real.log x : Complex)) =
    (x : Complex) ^ (z - 1) *
      (nicolasReflectedTail A b x : Complex)
  rw [hExp]
  push_cast
  calc
    ((x ^ (-1 : Real) : Real) : Complex) *
          (nicolasReflectedTail A b x : Complex) * (x : Complex) ^ z =
        (((x ^ (-1 : Real) : Real) : Complex) * (x : Complex) ^ z) *
          (nicolasReflectedTail A b x : Complex) := by ring
    _ = ((x : Complex) ^ ((-1 : Real) : Complex) *
          (x : Complex) ^ z) *
          (nicolasReflectedTail A b x : Complex) := by
      rw [Complex.ofReal_cpow hxPos.le]
    _ = (x : Complex) ^ (((-1 : Real) : Complex) + z) *
          (nicolasReflectedTail A b x : Complex) := by
      rw [Complex.cpow_add _ _ hxNe]
    _ = (x : Complex) ^ (z - 1) *
          (nicolasReflectedTail A b x : Complex) := by
      congr 2
      norm_num [sub_eq_add_neg, add_comm]

theorem nicolasReflectedComplexMellin_eq_continuation_of_re_neg
    {X A b : Real} (hX : 3 <= X) (hb : 0 < b)
    {z : Complex} (hz : z.re < 0) :
    nicolasReflectedComplexMellin X A b z =
      nicolasReflectedComplexContinuation X A b z := by
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hPower := nicolasLandauRpowComplexTailMellin_integrableOn hXPos (hz.trans hb)
  have hJ := (nicolasJ_complexMellin_integrableOn_Ioi_three hz).mono_set
    (Ioi_subset_Ioi hX)
  have hOld : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (nicolasLandauPositiveTail b x : Complex)) (Ioi X) := by
    have hSum : IntegrableOn (fun x : Real =>
        (x : Complex) ^ (z - 1) * (nicolasJ x : Complex) +
          (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) (Ioi X) :=
      hJ.add hPower
    apply hSum.congr_fun
    . intro x _
      unfold nicolasLandauPositiveTail
      push_cast
      ring
    . exact measurableSet_Ioi
  unfold nicolasReflectedComplexMellin
  calc
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        (x : Complex) ^ (z - 1) * (nicolasReflectedTail A b x : Complex)) =
        integral (volume.restrict (Ioi X)) (fun x : Real =>
          ((A + 1 : Real) : Complex) *
              ((x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) -
            (x : Complex) ^ (z - 1) * (nicolasLandauPositiveTail b x : Complex)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      unfold nicolasReflectedTail nicolasLandauPositiveTail
      push_cast
      ring
    _ = ((A + 1 : Real) : Complex) * nicolasLandauRpowComplexContinuation X b z -
        nicolasLandauPositiveComplexMellin X b z := by
      rw [integral_sub (hPower.const_mul ((A + 1 : Real) : Complex)) hOld,
        integral_const_mul, nicolasLandauRpowComplexTailMellin_eq_continuation
          hXPos (hz.trans hb)]
      rfl
    _ = nicolasReflectedComplexContinuation X A b z := by
      unfold nicolasReflectedComplexContinuation
      rw [nicolasLandauPositiveComplexMellin_eq_continuation_of_re_neg hX hb hz]

theorem nicolasReflectedComplexMGF_eq_continuation_of_re_neg
    {X A b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x -> 0 <= nicolasReflectedTail A b x)
    {z : Complex} (hz : z.re < 0) :
    complexMGF (fun x : Real => Real.log x) (nicolasReflectedMeasure X A b) z =
      nicolasReflectedComplexContinuation X A b z := by
  rw [complexMGF_log_nicolasReflectedMeasure_eq_complexMellin hX hPos]
  exact nicolasReflectedComplexMellin_eq_continuation_of_re_neg hX hb hz

/-- The negative real half-line is handled using the reflected measure's own MGF. -/
theorem nicolasReflectedMellinContinuation_analyticAt_neg
    {X A b sigma : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x -> 0 <= nicolasReflectedTail A b x)
    (hSigma : sigma < 0) :
    AnalyticAt Real (nicolasReflectedMellinContinuation X A b) sigma := by
  have hBelow : forall a : Real, a < 0 ->
      IntegrableOn (fun x : Real => x ^ (a - 1) * nicolasReflectedTail A b x)
        (Ioi X) := by
    intro a ha
    exact nicolasReflectedTail_integrableOn_of_neg hX hb ha
  have hInterior := interior_integrableExpSet_log_nicolasReflected_of_below
    hX hPos hBelow sigma hSigma
  have hMgf : AnalyticAt Real
      (mgf (fun x : Real => Real.log x) (nicolasReflectedMeasure X A b)) sigma :=
    analyticAt_mgf hInterior
  have hEq : Filter.EventuallyEq (nhds sigma)
      (mgf (fun x : Real => Real.log x) (nicolasReflectedMeasure X A b))
      (nicolasReflectedMellinContinuation X A b) := by
    filter_upwards [Iio_mem_nhds hSigma] with a ha
    rw [mgf_log_nicolasReflectedMeasure_eq_mellin hX hPos]
    exact nicolasReflectedMellin_eq_continuation_of_neg hX hb ha
  exact (analyticAt_congr hEq).mp hMgf

theorem nicolasReflectedMellinContinuation_analyticAt_lt
    {X A b sigma : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x -> 0 <= nicolasReflectedTail A b x)
    (hSigma : sigma < b) :
    AnalyticAt Real (nicolasReflectedMellinContinuation X A b) sigma := by
  rcases lt_trichotomy sigma 0 with hsNeg | hsZero | hsPos
  . exact nicolasReflectedMellinContinuation_analyticAt_neg hX hb hPos hsNeg
  . subst sigma
    have hPower := nicolasLandauRpowMellinContinuation_analyticAt
      (X := X) (b := b) (sigma := (0 : Real))
      (lt_of_lt_of_le (by norm_num) hX) hb
    have hPlus := nicolasLandauPositiveMellinContinuationFilled_analyticAt_zero hX hb
    unfold nicolasReflectedMellinContinuation
    exact (analyticAt_const.mul hPower).sub hPlus
  . have hPower := nicolasLandauRpowMellinContinuation_analyticAt
      (X := X) (b := b) (sigma := sigma)
      (lt_of_lt_of_le (by norm_num) hX) hSigma
    have hPlus := nicolasLandauPositiveMellinContinuationFilled_analyticAt_pos
      hX hsPos (lt_of_lt_of_le hSigma hbHalf) hSigma
    unfold nicolasReflectedMellinContinuation
    exact (analyticAt_const.mul hPower).sub hPlus

theorem Iio_subset_interior_integrableExpSet_nicolasReflected
    {X A b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x -> 0 <= nicolasReflectedTail A b x) :
    Iio b <= interior
      (integrableExpSet (fun x : Real => Real.log x) (nicolasReflectedMeasure X A b)) := by
  have hBelow : forall a : Real, a < 0 ->
      IntegrableOn (fun x : Real => x ^ (a - 1) * nicolasReflectedTail A b x)
        (Ioi X) := by
    intro a ha
    exact nicolasReflectedTail_integrableOn_of_neg hX hb ha
  apply Iio_subset_interior_integrableExpSet_of_analyticContinuation
    (H := nicolasReflectedMellinContinuation X A b)
    (ae_log_nonneg_nicolasReflectedMeasure hX)
  . exact interior_integrableExpSet_log_nicolasReflected_of_below hX hPos hBelow
  . intro sigma hs
    exact nicolasReflectedMellinContinuation_analyticAt_lt hX hb hbHalf hPos hs
  . intro a ha
    rw [mgf_log_nicolasReflectedMeasure_eq_mellin hX hPos]
    exact nicolasReflectedMellin_eq_continuation_of_neg hX hb ha

theorem nicolasReflectedComplexMGF_analyticAt
    {X A b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x -> 0 <= nicolasReflectedTail A b x)
    {z : Complex} (hz : z.re < b) :
    AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x) (nicolasReflectedMeasure X A b)) z := by
  apply analyticAt_complexMGF
  exact Iio_subset_interior_integrableExpSet_nicolasReflected hX hb hbHalf hPos hz

end

end PrimeFactorOscillations
