/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeWaveLimits

/-! # A global actual deleted-mass majorant for the count transfer -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter

theorem primeWaveMass_power_bound (b A : Real) (f : Real -> Real)
    (hb : 0 < b) (hf : forall v : Real, abs (f v) <= A)
    (hsource : Tendsto (fun x : Real =>
      (primeClassThetaReal Set.univ x - x) / x ^ b - f (Real.log x))
      atTop (nhds 0)) :
    exists C : Real, And (0 <= C) (forall x : Real, 2 <= x ->
      primeClassThetaReal greedyDeletedPrimeClass x <= C * x ^ b) := by
  choose X hX using Metric.tendsto_atTop.mp (primeWaveMass_limit b A f hb hf hsource)
    1 (by norm_num)
  let Y := max 2 X
  let C := A + 1 + greedyPrimeRegulatorReal Y + Real.log Y
  have hY : 2 <= Y := le_max_left 2 X
  have hA : 0 <= A := (abs_nonneg (f 0)).trans (hf 0)
  have hR := greedyPrimeRegulatorReal_nonneg Y
  have hl : 0 <= Real.log Y := Real.log_nonneg (by linarith only [hY])
  have hC : 0 <= C := by dsimp [C]; linarith only [hA, hR, hl]
  refine Exists.intro C (And.intro hC ?_)
  intro x hx
  have hx0 : 0 < x := by linarith only [hx]
  have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
  by_cases hxy : Y <= x
  case pos =>
    have hsmall : abs (primeClassThetaReal greedyDeletedPrimeClass x / x ^ b -
        dampedWaveEnvelope b f (Real.log x)) < 1 := by
      simpa only [Real.dist_eq, sub_zero] using hX x ((le_max_right 2 X).trans hxy)
    have henvelope := dampedWaveEnvelope_le b A f hb.le hf (Real.log x)
    have hu := (abs_lt.mp hsmall).2
    have hratio : primeClassThetaReal greedyDeletedPrimeClass x / x ^ b <= A + 1 := by
      linarith only [henvelope, hu]
    have hmul := mul_le_mul_of_nonneg_right hratio hxb.le
    have hcancel : (primeClassThetaReal greedyDeletedPrimeClass x / x ^ b) * x ^ b =
        primeClassThetaReal greedyDeletedPrimeClass x := by field_simp
    rw [hcancel] at hmul
    have hallow : A + 1 <= C := by dsimp [C]; linarith only [hR, hl]
    exact hmul.trans (mul_le_mul_of_nonneg_right hallow hxb.le)
  case neg =>
    have hxY : x <= Y := le_of_lt (lt_of_not_ge hxy)
    have hmass := (greedyDeletedPrimeClass_real_record_bounds x hx).2
    have hmono := greedyPrimeRegulatorReal_mono x Y hx0.le hxY
    have hlogs := Real.log_le_log hx0 hxY
    have hone : 1 <= x ^ b := Real.one_le_rpow (by linarith only [hx]) hb.le
    have hlarge := mul_le_mul_of_nonneg_left hone (add_nonneg hR hl)
    have hallow : greedyPrimeRegulatorReal Y + Real.log Y <= C := by
      dsimp [C]
      linarith only [hA]
    have hlast := mul_le_mul_of_nonneg_right hallow hxb.le
    linarith only [hmass, hmono, hlogs, hlarge, hlast]

end PrimeFactorOscillations.PrimeClassDeletion
