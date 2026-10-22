/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassAbelLimit
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeWaveMassBounds

/-! # The wave asymptotic for the actual deleted-prime count -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter
open PrimeFactorOscillations.PrimeClassSampling

theorem primeWaveCount_limit (b A : Real) (f : Real -> Real)
    (hb : 0 < b) (hf : forall v : Real, abs (f v) <= A)
    (hsource : Tendsto (fun x : Real =>
      (primeClassThetaReal Set.univ x - x) / x ^ b - f (Real.log x))
      atTop (nhds 0)) :
    Tendsto (fun x : Real =>
      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) * Real.log x /
        x ^ b - dampedWaveEnvelope b f (Real.log x)) atTop (nhds 0) := by
  choose C hC using primeWaveMass_power_bound b A f hb hf hsource
  have hrem := primeClassAbel_normalized_tendsto_zero greedyDeletedPrimeClass b C hb hC.1 hC.2
  have hmass := primeWaveMass_limit b A f hb hf hsource
  have h := hrem.add hmass
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  have hx0 : 0 < x := by linarith only [hx]
  have hl : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
  rw [primeClassCount_abel greedyDeletedPrimeClass x hx]
  field_simp
  ring

theorem primeWaveCount_div_limit (b A : Real) (f : Real -> Real)
    (hb : 0 < b) (hf : forall v : Real, abs (f v) <= A)
    (hsource : Tendsto (fun x : Real =>
      (primeClassThetaReal Set.univ x - x) / x ^ b - f (Real.log x))
      atTop (nhds 0)) :
    Tendsto (fun x : Real =>
      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) /
        (x ^ b / Real.log x) - dampedWaveEnvelope b f (Real.log x))
      atTop (nhds 0) := by
  apply (primeWaveCount_limit b A f hb hf hsource).congr'
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  have hx0 : 0 < x := by linarith only [hx]
  have hl : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
  field_simp

end PrimeFactorOscillations.PrimeClassDeletion
