/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import PrimeFactorOscillations.Helpers.PrimeProfileThetaClock
import PrimeFactorOscillations.Helpers.QuadraticRatioWave

/-!
# Quantitative probability-ratio wave error

The actual floor rank grows as alpha times nu times loglog N. Every remainder gives a uniform inverse-loglog bound.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Asymptotics Robin1984
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations.QuadraticPrimeLaw

theorem tendsto_referenceClock_div_loglog (law : QuadraticPrimeLaw) :
    Tendsto (fun N : Nat => law.referenceClock N / Real.log (Real.log (N : Real)))
      atTop (nhds law.nu) := by
  have hLL : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hD : Tendsto (fun N : Nat => Real.eulerMascheroniConstant +
      (Real.log (Real.log (Chebyshev.theta (N : Real))) - Real.log (Real.log (N : Real))))
      atTop (nhds Real.eulerMascheroniConstant) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_primeProfile_loglogTheta_sub_loglog)
  have hQuot := hD.div_atTop hLL
  have hOne : Tendsto (fun N : Nat =>
      (Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta (N : Real)))) /
        Real.log (Real.log (N : Real))) atTop (nhds 1) := by
    have h := hQuot.add_const 1
    norm_num only [zero_add] at h
    apply h.congr'
    filter_upwards [hLL.eventually_ne_atTop 0] with N hN
    field_simp [hN]
    ring
  simpa only [referenceClock, mul_div_assoc, mul_one] using hOne.const_mul law.nu

theorem tendsto_floorRank_div_loglog (law : QuadraticPrimeLaw)
    (alpha : Real) (ha : 0 < alpha) :
    Tendsto (fun N : Nat => (law.floorRank alpha N : Real) / Real.log (Real.log (N : Real)))
      atTop (nhds (alpha * law.nu)) := by
  have hL : Tendsto (fun N : Nat => alpha * law.referenceClock N) atTop atTop :=
    law.tendsto_referenceClock_atTop.const_mul_atTop ha
  have hF : Tendsto (fun N : Nat =>
      (law.floorRank alpha N : Real) / (alpha * law.referenceClock N)) atTop (nhds 1) := by
    simpa only [Function.comp_def, floorRank] using
      (tendsto_nat_floor_div_atTop :
        Tendsto (fun x : Real => (Nat.floor x : Real) / x) atTop (nhds 1)).comp hL
  have hA := (law.tendsto_referenceClock_div_loglog).const_mul alpha
  have h := hF.mul hA
  norm_num only [one_mul] at h
  apply h.congr'
  have hLL : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hL.eventually_ne_atTop 0, hLL.eventually_ne_atTop 0] with N hN hLog
  have hClock : Not (law.referenceClock N = 0) := by
    intro hz
    exact hN (by rw [hz, mul_zero])
  field_simp [ha.ne', hClock, hLog] <;> ring

theorem tendsto_loglog_div_floorRank (law : QuadraticPrimeLaw)
    (alpha : Real) (ha : 0 < alpha) :
    Tendsto (fun N : Nat => Real.log (Real.log (N : Real)) / (law.floorRank alpha N : Real))
      atTop (nhds (1 / (alpha * law.nu))) := by
  have hNe : Not (alpha * law.nu = 0) := mul_ne_zero ha.ne' law.nu_pos.ne'
  have h := (tendsto_const_nhds :
    Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1)).div
      (law.tendsto_floorRank_div_loglog alpha ha) hNe
  change Tendsto (fun N : Nat =>
    1 / ((law.floorRank alpha N : Real) / Real.log (Real.log (N : Real))))
    atTop (nhds (1 / (alpha * law.nu))) at h
  simpa only [one_div_div] using h

/-- A fully uniform bound for the normalized spectral error. -/
theorem exists_eventually_normalizedFloorRatioWave_spectral_error
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis) :
    exists A C : Real, 0 <= A /\ 0 <= C /\
      Filter.Eventually (fun N : Nat =>
        abs (law.normalizedFloorRatioWave alpha N - nicolasZeroWave (N : Real)) <=
          A / (law.floorRank alpha N : Real) +
          C * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real)) +
          nicolasLogSpectralConstant / Real.log (N : Real)) atTop := by
  choose K C hK hC hApprox using law.exists_eventually_normalizedFloorRatioWave_error alpha ha
  let beta := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  let B := nicolasLogSpectralConstant + 2 + abs beta
  have hBNonneg : 0 <= B := by
    dsimp only [B]
    linarith [nicolasLogSpectralConstant_pos, abs_nonneg beta]
  refine Exists.intro (K * B) (Exists.intro C (And.intro (mul_nonneg hK hBNonneg)
    (And.intro hC ?_)))
  have ht : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hApprox, ht.eventually (eventually_nicolasLog_normalized_wave_error hRH),
    ht.eventually_ge_atTop (Real.exp 1)] with N hA hS hExp
  let Y := (N : Real) ^ (1 / 2 : Real) * Real.log (N : Real) *
    nicolasLogMertensOscillation (N : Real)
  have hNOne : (1 : Real) < N :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hExp
  have hLog : 1 <= Real.log (N : Real) := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  have hDiv : nicolasLogSpectralConstant / Real.log (N : Real) <= nicolasLogSpectralConstant :=
    div_le_self nicolasLogSpectralConstant_pos.le hLog
  have hW := abs_nicolasZeroWave_le hRH hNOne
  change abs (nicolasZeroWave (N : Real)) <= beta at hW
  change abs (Y + 2 + nicolasZeroWave (N : Real)) <=
    nicolasLogSpectralConstant / Real.log (N : Real) at hS
  have hB : abs Y <= B := by
    apply abs_le.mpr
    dsimp [B]
    constructor <;> linarith only [(abs_le.mp hS).1, (abs_le.mp hS).2,
      (abs_le.mp hW).1, (abs_le.mp hW).2, hDiv, le_abs_self beta]
  have hr : (0 : Real) < law.floorRank alpha N := Nat.cast_pos.mpr hA.1
  have hScaled := mul_le_mul_of_nonneg_left hB
    (div_nonneg hK hr.le : 0 <= K / (law.floorRank alpha N : Real))
  have hFamily : abs (law.normalizedFloorRatioWave alpha N + 2 + Y) <=
      K * B / (law.floorRank alpha N : Real) +
        C * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real)) := by
    have he := hA.2.2.2
    change abs (law.normalizedFloorRatioWave alpha N + 2 + Y) <=
      K / (law.floorRank alpha N : Real) * abs Y + _ at he
    apply he.trans
    calc
      _ <= K / (law.floorRank alpha N : Real) * B +
          C * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real)) :=
        add_le_add hScaled (le_refl _)
      _ = _ := by ring
  have hTriangle := norm_sub_le
    (law.normalizedFloorRatioWave alpha N + 2 + Y)
    (Y + 2 + nicolasZeroWave (N : Real))
  have hCancel : (law.normalizedFloorRatioWave alpha N + 2 + Y) -
      (Y + 2 + nicolasZeroWave (N : Real)) =
      law.normalizedFloorRatioWave alpha N - nicolasZeroWave (N : Real) := by ring
  rw [hCancel] at hTriangle
  simp only [Real.norm_eq_abs] at hTriangle
  change abs (law.normalizedFloorRatioWave alpha N - nicolasZeroWave (N : Real)) <= _
  exact hTriangle.trans (add_le_add hFamily hS)

/-- The universal-wave approximation has the claimed inverse-loglog rate. -/
theorem exists_eventually_normalizedFloorRatioWave_error_div_loglog
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis) :
    exists K : Real, 0 <= K /\ Filter.Eventually (fun N : Nat =>
      0 < Real.log (Real.log (N : Real)) /\
      abs (law.normalizedFloorRatioWave alpha N - nicolasZeroWave (N : Real)) <=
        K / Real.log (Real.log (N : Real))) atTop := by
  choose A C hA hC hError using
    law.exists_eventually_normalizedFloorRatioWave_spectral_error alpha ha hRH
  have ht : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLog : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp ht
  have hLL : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLog
  have hLLRatio : Tendsto (fun N : Nat =>
      Real.log (Real.log (N : Real)) / Real.log (N : Real)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.rpow_one] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1)).tendsto_div_nhds_zero).comp hLog
  have hLogSq : Tendsto (fun N : Nat =>
      (Real.log (N : Real)) ^ 2 / (N : Real) ^ (1 / 2 : Real)) atTop (nhds 0) := by
    have h := ((isLittleO_log_rpow_rpow_atTop (2 : Real)
      (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero).comp ht
    simpa only [Function.comp_def, Real.rpow_two] using h
  have hTail : Tendsto (fun N : Nat =>
      Real.log (Real.log (N : Real)) * Real.log (N : Real) /
        (N : Real) ^ (1 / 2 : Real)) atTop (nhds 0) := by
    have h := hLLRatio.mul hLogSq
    norm_num only [mul_zero] at h
    apply h.congr'
    filter_upwards [hLog.eventually_ne_atTop 0] with N hN
    field_simp [hN] <;> ring
  let D : Nat -> Real := fun N =>
    A * (Real.log (Real.log (N : Real)) / (law.floorRank alpha N : Real)) +
      C * (Real.log (Real.log (N : Real)) * Real.log (N : Real) /
        (N : Real) ^ (1 / 2 : Real)) +
      nicolasLogSpectralConstant * (Real.log (Real.log (N : Real)) / Real.log (N : Real))
  let d : Real := A / (alpha * law.nu)
  have hD : Tendsto D atTop (nhds d) := by
    have hFirst := (law.tendsto_loglog_div_floorRank alpha ha).const_mul A
    have hSecond := hTail.const_mul C
    have hLast := hLLRatio.const_mul nicolasLogSpectralConstant
    simpa only [D, d, mul_zero, add_zero, div_eq_mul_inv, one_mul] using
      (hFirst.add hSecond).add hLast
  let K : Real := abs d + 1
  have hK : 0 <= K := by dsimp only [K]; linarith [abs_nonneg d]
  refine Exists.intro K (And.intro hK ?_)
  have hSmall := hD.eventually (eventually_le_nhds (by linarith : d < d + 1))
  filter_upwards [hError, hSmall, hLL.eventually_gt_atTop 0] with N he hDValue hPos
  refine And.intro hPos ?_
  have hScaled := mul_le_mul_of_nonneg_right he hPos.le
  have hProduct :
      (A / (law.floorRank alpha N : Real) +
        C * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real)) +
        nicolasLogSpectralConstant / Real.log (N : Real)) *
          Real.log (Real.log (N : Real)) = D N := by
    dsimp only [D]
    ring
  rw [hProduct] at hScaled
  have hConst : D N <= K := by dsimp only [K]; linarith [le_abs_self d]
  calc
    _ = (abs (law.normalizedFloorRatioWave alpha N - nicolasZeroWave (N : Real)) *
        Real.log (Real.log (N : Real))) / Real.log (Real.log (N : Real)) := by
      field_simp [hPos.ne']
    _ <= K / Real.log (Real.log (N : Real)) :=
      div_le_div_of_nonneg_right (hScaled.trans hConst) hPos.le

end PrimeFactorOscillations.QuadraticPrimeLaw
