/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeWaveRecordComparison

/-!
# Uniform prefix errors with the actual finite initial range retained

A pointwise tail estimate is not used as a uniform estimate over a growing
prefix. The bounded initial part is controlled explicitly by the regulator,
the nonnegative actual theta sum and the bound on the model wave.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

theorem primeClassThetaReal_nonneg (P : Set Nat) (x : Real) :
    0 <= primeClassThetaReal P x := by
  unfold primeClassThetaReal primeClassTheta
  apply Finset.sum_nonneg
  intro p hp
  have hp2 := (primeClassPrefix_mem_iff P (Nat.floor x) p).mp hp
  apply Real.log_nonneg
  exact_mod_cast (show 1 <= p by omega)

noncomputable def primeWaveInitialReserve (b A Y : Real) : Real :=
  greedyPrimeRegulatorReal Y + Real.log Y + Y + A * Y ^ b

theorem primeWaveInitialReserve_nonneg (b A Y : Real)
    (hA : 0 <= A) (hY : 2 <= Y) : 0 <= primeWaveInitialReserve b A Y := by
  have hR := greedyPrimeRegulatorReal_nonneg Y
  have hl : 0 <= Real.log Y := Real.log_nonneg (by linarith only [hY])
  have hp : 0 <= A * Y ^ b :=
    mul_nonneg hA (Real.rpow_nonneg (by linarith only [hY]) b)
  unfold primeWaveInitialReserve
  linarith only [hR, hl, hY, hp]

theorem primeWave_initial_error_bound (b A Y : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A) (hY : 2 <= Y)
    (t : Real) (ht : 2 <= t) (htY : t <= Y) :
    abs ((primeClassThetaReal Set.univ t - t) - t ^ b * f (Real.log t)) <=
      primeWaveInitialReserve b A Y := by
  have ht0 : 0 < t := by linarith only [ht]
  have hA : 0 <= A := (abs_nonneg (f 0)).trans (hf 0)
  have hR := greedyPrimeRegulatorReal_nonneg Y
  have hl : 0 <= Real.log Y := Real.log_nonneg (by linarith only [hY])
  have htheta := primeClassThetaReal_nonneg Set.univ t
  have hE := primeThetaErrorReal_le_record_log t ht
  have hmono := greedyPrimeRegulatorReal_mono t Y ht0.le htY
  have hlogs := Real.log_le_log ht0 htY
  have hpower := Real.rpow_le_rpow ht0.le htY hb
  have hp := mul_le_mul_of_nonneg_right hpower hA
  have hfa := abs_le.mp (hf (Real.log t))
  have hfl := mul_le_mul_of_nonneg_left hfa.1 (Real.rpow_pos_of_pos ht0 b).le
  have hfu := mul_le_mul_of_nonneg_left hfa.2 (Real.rpow_pos_of_pos ht0 b).le
  unfold primeWaveInitialReserve
  exact abs_le.mpr (And.intro
    (by nlinarith only [htheta, htY, hR, hl, hfu, hp])
    (by nlinarith only [hE, hmono, hlogs, htY, ht, hfl, hp]))

theorem primeWave_prefix_error_bound (b A e Y x : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A)
    (he : 0 <= e) (hY : 2 <= Y)
    (htail : forall t : Real, Y <= t ->
      abs ((primeClassThetaReal Set.univ t - t) / t ^ b - f (Real.log t)) <= e)
    (t : Real) (ht : 2 <= t) (htx : t <= x) :
    abs ((primeClassThetaReal Set.univ t - t) - t ^ b * f (Real.log t)) <=
      e * x ^ b + primeWaveInitialReserve b A Y := by
  have ht0 : 0 < t := by linarith only [ht]
  have hx0 := ht0.trans_le htx
  have hA : 0 <= A := (abs_nonneg (f 0)).trans (hf 0)
  have hC := primeWaveInitialReserve_nonneg b A Y hA hY
  by_cases htY : Y <= t
  case pos =>
    have hpow : 0 < t ^ b := Real.rpow_pos_of_pos ht0 b
    have hid : (primeClassThetaReal Set.univ t - t) - t ^ b * f (Real.log t) =
        ((primeClassThetaReal Set.univ t - t) / t ^ b - f (Real.log t)) * t ^ b := by
      field_simp
    rw [hid, abs_mul, abs_of_pos hpow]
    have hmodel := mul_le_mul_of_nonneg_right (htail t htY) hpow.le
    have hpower := Real.rpow_le_rpow ht0.le htx hb
    have hbound := mul_le_mul_of_nonneg_left hpower he
    linarith only [hmodel, hbound, hC]
  case neg =>
    have hbound := primeWave_initial_error_bound b A Y f hb hf hY t ht
      (le_of_lt (lt_of_not_ge htY))
    have hex : 0 <= e * x ^ b := mul_nonneg he (Real.rpow_pos_of_pos hx0 b).le
    linarith only [hbound, hex]

end PrimeFactorOscillations.PrimeClassDeletion
