/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeWaveInitialRange

/-!
# Actual prime-record and deleted-mass wave asymptotics

The input is the whole real-cutoff theta error, divided by its prescribed
power. A single hypothetical zeta zero is not an input to this theorem.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter

theorem primeWave_log_div_power_tendsto (b : Real) (hb : 0 < b) :
    Tendsto (fun x : Real => Real.log x / x ^ b) atTop (nhds 0) :=
  (isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero

theorem primeWaveRecord_limit (b A : Real) (f : Real -> Real)
    (hb : 0 < b) (hf : forall v : Real, abs (f v) <= A)
    (hsource : Tendsto (fun x : Real =>
      (primeClassThetaReal Set.univ x - x) / x ^ b - f (Real.log x))
      atTop (nhds 0)) :
    Tendsto (fun x : Real => greedyPrimeRegulatorReal x / x ^ b -
      dampedWaveEnvelope b f (Real.log x)) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro e he
  choose Y0 hY0 using Metric.tendsto_atTop.mp hsource (e / 4) (by linarith only [he])
  let Y := max 2 Y0
  let C := primeWaveInitialReserve b A Y
  have hY : 2 <= Y := le_max_left 2 Y0
  have hA : 0 <= A := (abs_nonneg (f 0)).trans (hf 0)
  have hC : 0 <= C := primeWaveInitialReserve_nonneg b A Y hA hY
  have htail : forall t : Real, Y <= t ->
      abs ((primeClassThetaReal Set.univ t - t) / t ^ b - f (Real.log t)) <= e / 4 := by
    intro t ht
    have h := hY0 t ((le_max_right 2 Y0).trans ht)
    have h' : abs ((primeClassThetaReal Set.univ t - t) / t ^ b -
        f (Real.log t)) < e / 4 := by
      simpa only [Real.dist_eq, sub_zero] using h
    exact h'.le
  have hconstant := (tendsto_rpow_atTop hb).const_div_atTop (C + A * (2 : Real) ^ b)
  have hlog := primeWave_log_div_power_tendsto b hb
  have hrem : Tendsto (fun x : Real =>
      (C + Real.log x + A * (2 : Real) ^ b) / x ^ b) atTop (nhds 0) := by
    have h := hconstant.add hlog
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [] with x
    ring
  choose X hX using Metric.tendsto_atTop.mp hrem (e / 4) (by linarith only [he])
  refine Exists.intro (max 2 X) ?_
  intro x hx
  have hx2 : 2 <= x := (le_max_left 2 X).trans hx
  have hx0 : 0 < x := by linarith only [hx2]
  have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
  have hD : 0 <= (e / 4) * x ^ b + C :=
    add_nonneg (mul_nonneg (by linarith only [he]) hxb.le) hC
  have herr := primeWaveRecord_model_error b A ((e / 4) * x ^ b + C) x f hb.le hf hD hx2
    (primeWave_prefix_error_bound b A (e / 4) Y x f hb.le hf
      (by linarith only [he]) hY htail)
  have hdiv := div_le_div_of_nonneg_right herr hxb.le
  have hid : abs (greedyPrimeRegulatorReal x / x ^ b -
      dampedWaveEnvelope b f (Real.log x)) =
      abs (greedyPrimeRegulatorReal x - x ^ b * dampedWaveEnvelope b f (Real.log x)) /
        x ^ b := by
    rw [show greedyPrimeRegulatorReal x / x ^ b - dampedWaveEnvelope b f (Real.log x) =
      (greedyPrimeRegulatorReal x - x ^ b * dampedWaveEnvelope b f (Real.log x)) /
        x ^ b by field_simp]
    rw [abs_div, abs_of_pos hxb]
  have hsplit : (((e / 4) * x ^ b + C) + Real.log x + A * (2 : Real) ^ b) / x ^ b =
      e / 4 + (C + Real.log x + A * (2 : Real) ^ b) / x ^ b := by
    field_simp <;> ring
  rw [hsplit] at hdiv
  have hsmall := hX x ((le_max_right 2 X).trans hx)
  have hsmallabs : abs ((C + Real.log x + A * (2 : Real) ^ b) / x ^ b) < e / 4 := by
    simpa only [Real.dist_eq, sub_zero] using hsmall
  have hsmall' : (C + Real.log x + A * (2 : Real) ^ b) / x ^ b < e / 4 :=
    (le_abs_self _).trans_lt hsmallabs
  rw [Real.dist_eq, sub_zero, hid]
  linarith only [hdiv, hsmall', he]

theorem primeWaveMass_limit (b A : Real) (f : Real -> Real)
    (hb : 0 < b) (hf : forall v : Real, abs (f v) <= A)
    (hsource : Tendsto (fun x : Real =>
      (primeClassThetaReal Set.univ x - x) / x ^ b - f (Real.log x))
      atTop (nhds 0)) :
    Tendsto (fun x : Real => primeClassThetaReal greedyDeletedPrimeClass x / x ^ b -
      dampedWaveEnvelope b f (Real.log x)) atTop (nhds 0) := by
  have hlog := primeWave_log_div_power_tendsto b hb
  have hovershoot : Tendsto (fun x : Real =>
      (primeClassThetaReal greedyDeletedPrimeClass x - greedyPrimeRegulatorReal x) /
        x ^ b) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
    case hgf =>
      filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
      exact div_nonneg (sub_nonneg.mpr (greedyDeletedPrimeClass_real_record_bounds x hx).1)
        (Real.rpow_nonneg (by linarith only [hx]) b)
    case hfh =>
      filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
      have h := (greedyDeletedPrimeClass_real_record_bounds x hx).2
      exact div_le_div_of_nonneg_right (by linarith only [h])
        (Real.rpow_nonneg (by linarith only [hx]) b)
  have h := hovershoot.add (primeWaveRecord_limit b A f hb hf hsource)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with x
  ring

end PrimeFactorOscillations.PrimeClassDeletion
