/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeRHUpper
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeSparseCriterion

/-!
# RH from cofinally many sparse greedy deletion counts

The maintained RH theta estimate controls every allowance in the actual
count bound. The unconditional uniform zero response supplies the converse.
The cutoffs are arbitrary integers, and epsilon is any positive real.
The larger paper theorem for every upper zero strip is a separate claim.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem greedyDeletedPrimeClass_eventually_power_count_of_RH
    (hRH : RiemannHypothesis) (epsilon : Real) (he : 0 < epsilon) :
    Filter.Eventually (fun n : Nat =>
      ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) <=
        (n : Real) ^ ((1 / 2 : Real) + epsilon)) atTop := by
  choose A hA C hC hCount using greedyDeletedPrimeClass_RH_count_mass_bound hRH
  let a : Real := (1 / 2 : Real) + epsilon
  let delta : Real := epsilon / 2
  have ha : 0 < a := by dsimp only [a]; linarith only [he]
  have hd : 0 < delta := by dsimp only [delta]; linarith only [he]
  have hLog : Tendsto (fun X : Real => Real.log X / X ^ delta)
      atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      gaussian_power_log_ratio_tendsto 0 delta hd
  have hSquare : Tendsto (fun X : Real =>
      Real.sqrt X * (Real.log X) ^ 2 / X ^ a) atTop (nhds 0) := by
    have h := hLog.mul hLog
    have h' : Tendsto (fun X : Real =>
        (Real.log X / X ^ delta) * (Real.log X / X ^ delta))
        atTop (nhds 0) := by simpa only [mul_zero] using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with X hX
    have hExponent : a = (1 / 2 : Real) + delta + delta := by
      dsimp only [a, delta]
      ring
    rw [Real.sqrt_eq_rpow, hExponent, Real.rpow_add hX, Real.rpow_add hX]
    have hHalf : Not (X ^ (1 / 2 : Real) = 0) :=
      (Real.rpow_pos_of_pos hX (1 / 2 : Real)).ne'
    have hDelta : Not (X ^ delta = 0) := (Real.rpow_pos_of_pos hX delta).ne'
    field_simp [hHalf, hDelta]
  have hConstant : Tendsto (fun X : Real => A / X ^ a) atTop (nhds 0) :=
    (tendsto_rpow_atTop ha).const_div_atTop A
  have hLast : Tendsto (fun X : Real => Real.log X / X ^ a) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      gaussian_power_log_ratio_tendsto 0 a ha
  have hSum : Tendsto (fun X : Real =>
      A / X ^ a + C * (Real.sqrt X * (Real.log X) ^ 2 / X ^ a) +
        Real.log X / X ^ a) atTop (nhds 0) := by
    simpa only [mul_zero, zero_add, add_zero] using
      (hConstant.add (hSquare.const_mul C)).add hLast
  have hTotal : Tendsto (fun X : Real =>
      (A + C * Real.sqrt X * (Real.log X) ^ 2 + Real.log X) / X ^ a)
      atTop (nhds 0) := by
    apply hSum.congr'
    exact Filter.Eventually.of_forall (fun X => by ring)
  have hNat : Tendsto (fun n : Nat =>
      (A + C * Real.sqrt (n : Real) * (Real.log (n : Real)) ^ 2 +
        Real.log (n : Real)) / (n : Real) ^ a) atTop (nhds 0) :=
    hTotal.comp tendsto_natCast_atTop_atTop
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  filter_upwards [hNat.eventually (eventually_lt_nhds hLogTwo),
    eventually_ge_atTop (2 : Nat)] with n hSmall hn
  have hnPos : (0 : Real) < (n : Real) := by exact_mod_cast (by omega : 0 < n)
  have hPower : 0 < (n : Real) ^ a := Real.rpow_pos_of_pos hnPos a
  have hMul := mul_lt_mul_of_pos_right hSmall hPower
  have hCancel : ((A + C * Real.sqrt (n : Real) * (Real.log (n : Real)) ^ 2 +
      Real.log (n : Real)) / (n : Real) ^ a) * (n : Real) ^ a =
        A + C * Real.sqrt (n : Real) * (Real.log (n : Real)) ^ 2 +
          Real.log (n : Real) := by field_simp [hPower.ne']
  rw [hCancel] at hMul
  have hBound := hCount n hn
  by_contra hFail
  have hWrong := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hFail)) hLogTwo.le
  change (n : Real) ^ a * Real.log 2 <=
    ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) * Real.log 2 at hWrong
  linarith only [hWrong, hBound, hMul]

theorem riemannHypothesis_iff_cofinal_greedyDeletedPrimeClass_count :
    RiemannHypothesis <-> (forall epsilon : Real, 0 < epsilon -> forall N : Nat,
      Exists fun n : Nat => And (max N 2 <= n)
        (((primeClassPrefix greedyDeletedPrimeClass n).card : Real) <=
          (n : Real) ^ ((1 / 2 : Real) + epsilon))) := by
  constructor
  case mp =>
    intro hRH epsilon he N
    choose M hM using Filter.eventually_atTop.mp
      (greedyDeletedPrimeClass_eventually_power_count_of_RH hRH epsilon he)
    exact Exists.intro (max (max N 2) M)
      (And.intro (le_max_left _ _) (hM _ (le_max_right _ _)))
  case mpr =>
    exact riemannHypothesis_of_sparse_greedyDeletedPrimeClass_count

end PrimeFactorOscillations.PrimeClassDeletion
