/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauRightmostRay

/-!
# The reflected Nicolas measure

The reflected tail A*x^(-b)-J(x) and its real Mellin transform.
Measure transport is adapted from Robin1984 at
bfa72aec0c25c8ee29cefe4449d778ff30412bee (Apache-2.0).
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter MeasureTheory ProbabilityTheory Set Robin1984
open scoped ENNReal Topology

noncomputable section

def nicolasReflectedTail (A b x : Real) : Real :=
  A * x ^ (-b) - nicolasJ x

def nicolasReflectedDensity (A b x : Real) : ENNReal :=
  ENNReal.ofReal (x ^ (-1 : Real) * nicolasReflectedTail A b x)

def nicolasReflectedMeasure (X A b : Real) : Measure Real :=
  (volume.restrict (Ioi X)).withDensity (nicolasReflectedDensity A b)

def nicolasReflectedMellin (X A b a : Real) : Real :=
  integral (volume.restrict (Ioi X)) (fun x : Real =>
    x ^ (a - 1) * nicolasReflectedTail A b x)

def nicolasReflectedMellinContinuation (X A b a : Real) : Real :=
  (A + 1) * nicolasLandauRpowMellinContinuation X b a -
    nicolasLandauPositiveMellinContinuationFilled X b a

theorem nicolasReflectedDensity_aemeasurable
    {X A b : Real} (hX : 3 <= X) :
    AEMeasurable (nicolasReflectedDensity A b)
      (volume.restrict (Ioi X)) := by
  have hJ := nicolasJ_aemeasurable_restrict_Ioi hX
  have hInv : AEMeasurable (fun x : Real => x ^ (-1 : Real))
      (volume.restrict (Ioi X)) :=
    measurable_id.aemeasurable.pow aemeasurable_const
  have hPower : AEMeasurable (fun x : Real => x ^ (-b))
      (volume.restrict (Ioi X)) :=
    measurable_id.aemeasurable.pow aemeasurable_const
  exact (hInv.mul ((hPower.const_mul A).sub hJ)).ennreal_ofReal

theorem ae_log_nonneg_nicolasReflectedMeasure
    {X A b : Real} (hX : 3 <= X) :
    Filter.Eventually (fun x : Real => 0 <= Real.log x)
      (ae (nicolasReflectedMeasure X A b)) := by
  have hBase : Filter.Eventually (fun x : Real => 0 <= Real.log x)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.log_nonneg (le_trans (by norm_num) (hX.trans hx.le))
  exact (withDensity_absolutelyContinuous
    (volume.restrict (Ioi X)) (nicolasReflectedDensity A b)).ae_le hBase

theorem mgf_log_nicolasReflectedMeasure_eq_mellin
    {X A b a : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasReflectedTail A b x) :
    mgf (fun x : Real => Real.log x)
        (nicolasReflectedMeasure X A b) a =
      nicolasReflectedMellin X A b a := by
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
  unfold mgf nicolasReflectedMeasure
  rw [hMeasureEq, integral_withDensity_eq_integral_toReal_smul
    hDensity.measurable_mk hDensityTop]
  unfold nicolasReflectedMellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hTail : 0 <= nicolasReflectedTail A b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      nicolasReflectedTail A b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  change (measurableDensity x).toReal * Real.exp (a * Real.log x) =
    x ^ (a - 1) * nicolasReflectedTail A b x
  rw [<- hdx]
  unfold nicolasReflectedDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  rw [Real.rpow_def_of_pos hxPos, Real.rpow_def_of_pos hxPos]
  calc
    Real.exp (Real.log x * -1) * nicolasReflectedTail A b x *
        Real.exp (a * Real.log x) =
        (Real.exp (Real.log x * -1) *
          Real.exp (a * Real.log x)) *
            nicolasReflectedTail A b x := by ring
    _ = Real.exp (Real.log x * -1 + a * Real.log x) *
        nicolasReflectedTail A b x := by rw [Real.exp_add]
    _ = Real.exp (Real.log x * (a - 1)) *
        nicolasReflectedTail A b x := by
      congr 2
      ring

theorem mem_integrableExpSet_log_nicolasReflected_iff
    {X A b a : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasReflectedTail A b x) :
    Membership.mem
        (integrableExpSet (fun x : Real => Real.log x)
          (nicolasReflectedMeasure X A b)) a <->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * nicolasReflectedTail A b x) (Ioi X) := by
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
  change Integrable (fun x : Real => Real.exp (a * Real.log x))
      (nicolasReflectedMeasure X A b) <->
    Integrable (fun x : Real =>
      x ^ (a - 1) * nicolasReflectedTail A b x)
      (volume.restrict (Ioi X))
  unfold nicolasReflectedMeasure
  rw [hMeasureEq, integrable_withDensity_iff
    hDensity.measurable_mk hDensityTop]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hTail : 0 <= nicolasReflectedTail A b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      nicolasReflectedTail A b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  change Real.exp (a * Real.log x) * (measurableDensity x).toReal =
    x ^ (a - 1) * nicolasReflectedTail A b x
  rw [<- hdx]
  unfold nicolasReflectedDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  rw [Real.rpow_def_of_pos hxPos, Real.rpow_def_of_pos hxPos]
  calc
    Real.exp (a * Real.log x) *
        (Real.exp (Real.log x * -1) *
          nicolasReflectedTail A b x) =
        (Real.exp (a * Real.log x) *
          Real.exp (Real.log x * -1)) *
            nicolasReflectedTail A b x := by ring
    _ = Real.exp (a * Real.log x + Real.log x * -1) *
        nicolasReflectedTail A b x := by rw [Real.exp_add]
    _ = Real.exp (Real.log x * (a - 1)) *
        nicolasReflectedTail A b x := by
      congr 2
      ring

theorem interior_integrableExpSet_log_nicolasReflected_of_below
    {X A b sigma : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasReflectedTail A b x)
    (hBelow : forall a : Real, a < sigma ->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * nicolasReflectedTail A b x) (Ioi X)) :
    forall a : Real, a < sigma ->
      Membership.mem
        (interior (integrableExpSet (fun x : Real => Real.log x)
          (nicolasReflectedMeasure X A b))) a := by
  intro a ha
  rw [mem_interior_iff_mem_nhds]
  let eps : Real := (sigma - a) / 2
  have hEps : 0 < eps := by
    dsimp [eps]
    linarith
  apply mem_of_superset (Metric.ball_mem_nhds a hEps)
  intro y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hySigma : y < sigma := by
    have hAbs := (abs_lt.mp hy).2
    dsimp [eps] at hAbs
    linarith
  exact (mem_integrableExpSet_log_nicolasReflected_iff hX hPos).2
    (hBelow y hySigma)

theorem nicolasReflectedPower_integrableOn
    {X b a : Real} (hX : 0 < X) (ha : a < b) :
    IntegrableOn (fun x : Real => x ^ (a - 1) * x ^ (-b)) (Ioi X) := by
  have hBase : IntegrableOn (fun x : Real => x ^ (a - b - 1)) (Ioi X) := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hX
  apply hBase.congr_fun
  . intro x hx
    have hxPos : 0 < x := hX.trans hx
    change x ^ (a - b - 1) = x ^ (a - 1) * x ^ (-b)
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  . exact measurableSet_Ioi

theorem nicolasReflectedTail_integrableOn_of_neg
    {X A b a : Real} (hX : 3 <= X) (hb : 0 < b) (ha : a < 0) :
    IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasReflectedTail A b x) (Ioi X) := by
  have hPower := nicolasReflectedPower_integrableOn
    (lt_of_lt_of_le (by norm_num) hX) (ha.trans hb)
  have hOld := nicolasLandauPositiveTail_integrableOn_of_neg hX hb ha
  have hDifference : IntegrableOn (fun x : Real =>
      (A + 1) * (x ^ (a - 1) * x ^ (-b)) -
        x ^ (a - 1) * nicolasLandauPositiveTail b x) (Ioi X) :=
    (hPower.const_mul (A + 1)).sub hOld
  apply hDifference.congr_fun
  . intro x _
    unfold nicolasReflectedTail nicolasLandauPositiveTail
    ring
  . exact measurableSet_Ioi

theorem nicolasReflectedMellin_eq_continuation_of_neg
    {X A b a : Real} (hX : 3 <= X) (hb : 0 < b) (ha : a < 0) :
    nicolasReflectedMellin X A b a = nicolasReflectedMellinContinuation X A b a := by
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hPower := nicolasReflectedPower_integrableOn hXPos (ha.trans hb)
  have hOld := nicolasLandauPositiveTail_integrableOn_of_neg hX hb ha
  unfold nicolasReflectedMellin
  calc
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        x ^ (a - 1) * nicolasReflectedTail A b x) =
        integral (volume.restrict (Ioi X)) (fun x : Real =>
          (A + 1) * (x ^ (a - 1) * x ^ (-b)) -
            x ^ (a - 1) * nicolasLandauPositiveTail b x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      unfold nicolasReflectedTail nicolasLandauPositiveTail
      ring
    _ = (A + 1) * nicolasLandauRpowMellinContinuation X b a -
        nicolasLandauPositiveMellin X b a := by
      rw [integral_sub (hPower.const_mul (A + 1)) hOld, integral_const_mul,
        nicolasLandauRpowTailMellin_eq_continuation hXPos (ha.trans hb)]
      rfl
    _ = nicolasReflectedMellinContinuation X A b a := by
      unfold nicolasReflectedMellinContinuation
      rw [nicolasLandauPositiveMellin_eq_continuation_of_neg hX hb ha,
        nicolasLandauPositiveMellinContinuationFilled_eq_raw_of_neg hX ha]

end

end PrimeFactorOscillations
