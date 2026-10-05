/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauPositiveTail.lean
Original source lines 1524-1735. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPositiveTailMellin

/-!
# Measure and exponential-integrability transport for the positive tail

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem nicolasJ_aemeasurable_restrict_Ioi
    {X : Real} (hX : 3 <= X) :
    AEMeasurable nicolasJ (volume.restrict (Ioi X)) := by
  let q : Real -> Real := fun t : Real =>
    nicolasPsiError t * nicolasTailKernel t
  have hq : IntegrableOn q (Ioi (3 : Real)) := by
    simpa [q] using nicolasJKernel_integrableOn_Ioi_three
  let q0 : Real -> Real := (Ioi (3 : Real)).indicator q
  have hq0 : Integrable q0 volume := by
    dsimp [q0]
    exact hq.integrable_indicator measurableSet_Ioi
  let tailPrimitive : Real -> Real := fun x : Real =>
    integral (volume.restrict (Ioi (3 : Real))) q -
      intervalIntegral q0 3 x volume
  have hContinuous : Continuous tailPrimitive := by
    dsimp [tailPrimitive]
    exact continuous_const.sub (hq0.continuous_primitive 3)
  have hEq : Filter.Eventually
      (fun x : Real => nicolasJ x = tailPrimitive x)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxThree : 3 <= x := hX.trans hx.le
    have hqx : IntegrableOn q (Ioi x) :=
      hq.mono_set (Ioi_subset_Ioi hxThree)
    have hSplit := intervalIntegral.integral_interval_add_Ioi hq hqx
    have hInterval : intervalIntegral q0 3 x volume =
        intervalIntegral q 3 x volume := by
      apply intervalIntegral.integral_congr_Ioo_of_le hxThree
      intro t ht
      simpa [q, ht.1]
    unfold nicolasJ
    dsimp [tailPrimitive, q]
    rw [hInterval]
    linarith
  have hEqSymm : Filter.Eventually
      (fun x : Real => tailPrimitive x = nicolasJ x)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [hEq] with x hx
    exact hx.symm
  exact hContinuous.aemeasurable.congr hEqSymm

theorem nicolasLandauPositiveDensity_aemeasurable
    {X b : Real} (hX : 3 <= X) :
    AEMeasurable (nicolasLandauPositiveDensity b)
      (volume.restrict (Ioi X)) := by
  have hJ := nicolasJ_aemeasurable_restrict_Ioi hX
  have hInv : AEMeasurable (fun x : Real => x ^ (-1 : Real))
      (volume.restrict (Ioi X)) :=
    measurable_id.aemeasurable.pow aemeasurable_const
  have hPower : AEMeasurable (fun x : Real => x ^ (-b))
      (volume.restrict (Ioi X)) :=
    measurable_id.aemeasurable.pow aemeasurable_const
  exact (hInv.mul (hJ.add hPower)).ennreal_ofReal

theorem ae_log_nonneg_nicolasLandauPositiveMeasure
    {X b : Real} (hX : 3 <= X) :
    Filter.Eventually (fun x : Real => 0 <= Real.log x)
      (ae (nicolasLandauPositiveMeasure X b)) := by
  have hBase : Filter.Eventually (fun x : Real => 0 <= Real.log x)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.log_nonneg (le_trans (by norm_num) (hX.trans hx.le))
  exact (withDensity_absolutelyContinuous
    (volume.restrict (Ioi X)) (nicolasLandauPositiveDensity b)).ae_le hBase

theorem mgf_log_nicolasLandauPositiveMeasure_eq_mellin
    {X b a : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x) :
    mgf (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b) a =
      nicolasLandauPositiveMellin X b a := by
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
  unfold mgf nicolasLandauPositiveMeasure
  rw [hMeasureEq, integral_withDensity_eq_integral_toReal_smul
    hDensity.measurable_mk hDensityTop]
  unfold nicolasLandauPositiveMellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hTail : 0 <= nicolasLandauPositiveTail b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      nicolasLandauPositiveTail b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  change (measurableDensity x).toReal * Real.exp (a * Real.log x) =
    x ^ (a - 1) * nicolasLandauPositiveTail b x
  rw [<- hdx]
  unfold nicolasLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  rw [Real.rpow_def_of_pos hxPos, Real.rpow_def_of_pos hxPos]
  calc
    Real.exp (Real.log x * -1) * nicolasLandauPositiveTail b x *
        Real.exp (a * Real.log x) =
        (Real.exp (Real.log x * -1) *
          Real.exp (a * Real.log x)) *
            nicolasLandauPositiveTail b x := by ring
    _ = Real.exp (Real.log x * -1 + a * Real.log x) *
        nicolasLandauPositiveTail b x := by rw [Real.exp_add]
    _ = Real.exp (Real.log x * (a - 1)) *
        nicolasLandauPositiveTail b x := by
      congr 2
      ring

theorem mem_integrableExpSet_log_nicolasLandau_iff
    {X b a : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x) :
    Membership.mem
        (integrableExpSet (fun x : Real => Real.log x)
          (nicolasLandauPositiveMeasure X b)) a <->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * nicolasLandauPositiveTail b x) (Ioi X) := by
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
  change Integrable (fun x : Real => Real.exp (a * Real.log x))
      (nicolasLandauPositiveMeasure X b) <->
    Integrable (fun x : Real =>
      x ^ (a - 1) * nicolasLandauPositiveTail b x)
      (volume.restrict (Ioi X))
  unfold nicolasLandauPositiveMeasure
  rw [hMeasureEq, integrable_withDensity_iff
    hDensity.measurable_mk hDensityTop]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hTail : 0 <= nicolasLandauPositiveTail b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      nicolasLandauPositiveTail b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  change Real.exp (a * Real.log x) * (measurableDensity x).toReal =
    x ^ (a - 1) * nicolasLandauPositiveTail b x
  rw [<- hdx]
  unfold nicolasLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  rw [Real.rpow_def_of_pos hxPos, Real.rpow_def_of_pos hxPos]
  calc
    Real.exp (a * Real.log x) *
        (Real.exp (Real.log x * -1) *
          nicolasLandauPositiveTail b x) =
        (Real.exp (a * Real.log x) *
          Real.exp (Real.log x * -1)) *
            nicolasLandauPositiveTail b x := by ring
    _ = Real.exp (a * Real.log x + Real.log x * -1) *
        nicolasLandauPositiveTail b x := by rw [Real.exp_add]
    _ = Real.exp (Real.log x * (a - 1)) *
        nicolasLandauPositiveTail b x := by
      congr 2
      ring

theorem interior_integrableExpSet_log_nicolasLandau_of_below
    {X b sigma : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    (hBelow : forall a : Real, a < sigma ->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * nicolasLandauPositiveTail b x) (Ioi X)) :
    forall a : Real, a < sigma ->
      Membership.mem
        (interior (integrableExpSet (fun x : Real => Real.log x)
          (nicolasLandauPositiveMeasure X b))) a := by
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
  exact (mem_integrableExpSet_log_nicolasLandau_iff hX hPos).2
    (hBelow y hySigma)

end

end Robin1984

