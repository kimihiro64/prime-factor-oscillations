/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianRegulatorLower

/-!
# Real cutoff rescaling and the actual deleted-prime count

A positive power substitution covers every sufficiently large real
cutoff. The native deleted-mass comparison then loses only an
arbitrarily small power when its single logarithm is absorbed.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem greedyPrimeRegulatorReal_rescale_power_lower
    (s B d T : Real) (hs : 0 < s)
    (hSource : forall X : Real, T <= X ->
      d * X ^ B <= greedyPrimeRegulatorReal (X ^ s)) :
    Exists fun Y0 : Real => forall Y : Real, Y0 <= Y ->
      d * Y ^ (B / s) <= greedyPrimeRegulatorReal Y := by
  let U : Real := max 1 T
  have hU : 0 < U := lt_of_lt_of_le Real.zero_lt_one (le_max_left 1 T)
  refine Exists.intro (max 2 (Real.exp (s * Real.log U))) ?_
  intro Y hY0
  have hY2 : 2 <= Y := (le_max_left _ _).trans hY0
  have hYPos : 0 < Y := by linarith only [hY2]
  have hYScale := (le_max_right _ _).trans hY0
  have hLog := Real.log_le_log (Real.exp_pos (s * Real.log U)) hYScale
  rw [Real.log_exp] at hLog
  let X : Real := Real.exp (Real.log Y / s)
  have hXPos : 0 < X := Real.exp_pos _
  have hDiv := div_le_div_of_nonneg_right hLog hs.le
  have hUnit : (s * Real.log U) / s = Real.log U := by field_simp [hs.ne']
  rw [hUnit] at hDiv
  have hUX : U <= X := by
    have h := Real.exp_le_exp.mpr hDiv
    rw [Real.exp_log hU] at h
    exact h
  have hTX : T <= X := (le_max_right 1 T).trans hUX
  have hRescale : X ^ s = Y := by
    rw [Real.rpow_def_of_pos hXPos]
    dsimp only [X]
    rw [Real.log_exp]
    have hCancel : (Real.log Y / s) * s = Real.log Y := by field_simp [hs.ne']
    rw [hCancel, Real.exp_log hYPos]
  have hWeight : X ^ B = Y ^ (B / s) := by
    rw [Real.rpow_def_of_pos hXPos, Real.rpow_def_of_pos hYPos]
    dsimp only [X]
    rw [Real.log_exp]
    congr 1
    ring
  have h := hSource X hTX
  rw [hRescale, hWeight] at h
  exact h

theorem greedyDeletedPrimeClass_count_of_regulator_power_lower
    (r d epsilon T : Real) (hd : 0 < d) (he : 0 < epsilon)
    (hSource : forall Y : Real, T <= Y ->
      d * Y ^ r <= greedyPrimeRegulatorReal Y) :
    Exists fun Y0 : Real => forall Y : Real, Y0 <= Y ->
      d * Y ^ (r - epsilon) <=
        ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor Y)).card : Real) := by
  have hLogSmall := (isLittleO_log_rpow_atTop he).bound (by norm_num : (0 : Real) < 1)
  have hLogEvent : Filter.Eventually
      (fun Y : Real => Real.log Y <= Y ^ epsilon) atTop := by
    filter_upwards [hLogSmall, eventually_ge_atTop (2 : Real)] with Y hSmall hY
    have hPower := Real.rpow_nonneg (by linarith only [hY] : 0 <= Y) epsilon
    have h := hSmall
    simp only [one_mul, Real.norm_eq_abs, abs_of_nonneg hPower] at h
    exact (le_abs_self _).trans h
  choose T2 hT2 using Filter.eventually_atTop.mp hLogEvent
  refine Exists.intro (max 2 (max T T2)) ?_
  intro Y hY0
  have hY2 : 2 <= Y := (le_max_left _ _).trans hY0
  have hRest := (le_max_right 2 (max T T2)).trans hY0
  have hSource' := hSource Y ((le_max_left T T2).trans hRest)
  have hLog' := hT2 Y ((le_max_right T T2).trans hRest)
  have hRecord := (greedyDeletedPrimeClass_real_record_bounds Y hY2).1
  have hMass := primeClassThetaReal_le_count_mul_log greedyDeletedPrimeClass Y hY2
  let N : Real := ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor Y)).card : Real)
  have hN : 0 <= N := Nat.cast_nonneg _
  have hBound : d * Y ^ r <= N * Y ^ epsilon := by
    calc
      _ <= greedyPrimeRegulatorReal Y := hSource'
      _ <= primeClassThetaReal greedyDeletedPrimeClass Y := hRecord
      _ <= N * Real.log Y := hMass
      _ <= _ := mul_le_mul_of_nonneg_left hLog' hN
  have hYPos : 0 < Y := by linarith only [hY2]
  have hPower : 0 < Y ^ epsilon := Real.rpow_pos_of_pos hYPos epsilon
  have hSplit : (d * Y ^ (r - epsilon)) * Y ^ epsilon = d * Y ^ r := by
    rw [mul_assoc, <- Real.rpow_add hYPos]
    congr 1
    congr 1
    ring
  change d * Y ^ (r - epsilon) <= N
  by_contra hFail
  have hLess := mul_lt_mul_of_pos_right (lt_of_not_ge hFail) hPower
  rw [hSplit] at hLess
  exact (not_lt_of_ge hBound) hLess

end PrimeFactorOscillations.PrimeClassDeletion
