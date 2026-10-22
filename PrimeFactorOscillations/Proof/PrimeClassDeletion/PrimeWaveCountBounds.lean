/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeWaveCount

/-! # Uniform count bounds from a positive wave envelope -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter
open PrimeFactorOscillations.PrimeClassSampling

theorem primeWaveCount_uniform_bounds (b A c : Real) (f : Real -> Real)
    (hb : 0 < b) (hf : forall v : Real, abs (f v) <= A) (hc : 0 < c)
    (henvelope : forall v : Real, c <= dampedWaveEnvelope b f v)
    (hsource : Tendsto (fun x : Real =>
      (primeClassThetaReal Set.univ x - x) / x ^ b - f (Real.log x))
      atTop (nhds 0)) :
    exists X : Real, And (2 <= X) (forall x : Real, X <= x ->
      And ((c / 2) * (x ^ b / Real.log x) <=
        ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real))
        (((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) <=
          (A + 1) * (x ^ b / Real.log x))) := by
  have he : 0 < min (c / 2) 1 := lt_min (by linarith only [hc]) (by norm_num)
  choose X hX using Metric.tendsto_atTop.mp (primeWaveCount_div_limit b A f hb hf hsource)
    (min (c / 2) 1) he
  refine Exists.intro (max 2 X) (And.intro (le_max_left 2 X) ?_)
  intro x hx
  have hx2 : 2 <= x := (le_max_left 2 X).trans hx
  have hx0 : 0 < x := by linarith only [hx2]
  have hl : 0 < Real.log x := Real.log_pos (by linarith only [hx2])
  have hscale : 0 < x ^ b / Real.log x := div_pos (Real.rpow_pos_of_pos hx0 b) hl
  have hsmall : abs (
      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) /
        (x ^ b / Real.log x) - dampedWaveEnvelope b f (Real.log x)) < min (c / 2) 1 := by
    simpa only [Real.dist_eq, sub_zero] using hX x ((le_max_right 2 X).trans hx)
  have hparts := abs_lt.mp hsmall
  have hpLow := henvelope (Real.log x)
  have hpHigh := dampedWaveEnvelope_le b A f hb.le hf (Real.log x)
  have heLow := min_le_left (c / 2) (1 : Real)
  have heHigh := min_le_right (c / 2) (1 : Real)
  have hnormLow : c / 2 <=
      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) /
        (x ^ b / Real.log x) := by linarith only [hparts.1, hpLow, heLow]
  have hnormHigh :
      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) /
        (x ^ b / Real.log x) <= A + 1 := by linarith only [hparts.2, hpHigh, heHigh]
  have hlow := mul_le_mul_of_nonneg_right hnormLow hscale.le
  have hhigh := mul_le_mul_of_nonneg_right hnormHigh hscale.le
  have hcancel :
      (((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) /
        (x ^ b / Real.log x)) * (x ^ b / Real.log x) =
      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) := by field_simp
  rw [hcancel] at hlow hhigh
  exact And.intro hlow hhigh

end PrimeFactorOscillations.PrimeClassDeletion
