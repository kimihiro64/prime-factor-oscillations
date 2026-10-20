/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.QuadraticRatioWave
import PrimeFactorOscillations.Helpers.XiZeroLogSpectrum
import PrimeFactorOscillations.Helpers.XiZeroMultiplicity
import PrimeFactorOscillations.Proof.DetectorPackets.RHFourierMean

/-!
# RHZeroReconstruction

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations

open Robin1984

theorem cpow_im_eq_logCharacter (v : Real) {x : Real} (hx : 0 < x) :
    (x : Complex) ^ ((v : Complex) * Complex.I) = logCharacter v x := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)),
    <- Complex.ofReal_log hx.le]
  unfold logCharacter
  congr 1
  ring

theorem logCharacter_pow (v x : Real) (k : Nat) :
    logCharacter v (x ^ k) = logCharacter ((k : Real) * v) x := by
  unfold logCharacter
  rw [Real.log_pow]
  congr 1 <;> push_cast <;> ring

theorem ofReal_re_logSpectrum {J : Type*} (a : J -> Real) (f : J -> Real)
    (ha : Summable (fun j : J => norm ((a j : Real) : Complex))) (x : Real) :
    (((logSpectrum (fun j => (a j : Complex)) f x).re : Real) : Complex) =
      (logSpectrum (fun j => (a j : Complex)) f x +
        logSpectrum (fun j => (a j : Complex)) (fun j => -f j) x) / 2 := by
  have hs := summable_logSpectrum (fun j => (a j : Complex)) f ha x
  have ht := summable_logSpectrum (fun j => (a j : Complex)) (fun j => -f j) ha x
  have hMap := (Complex.ofRealCLM.comp Complex.reCLM).map_tsum hs
  change (((tsum (fun j => (a j : Complex) * logCharacter (f j) x)).re : Real) : Complex) =
    tsum (fun j => ((((a j : Complex) * logCharacter (f j) x).re : Real) : Complex)) at hMap
  unfold logSpectrum
  rw [hMap, <- hs.tsum_add ht, <- tsum_div_const]
  apply tsum_congr
  intro j
  have hConj : logCharacter (-f j) x =
      (starRingEnd Complex) (logCharacter (f j) x) := by
    unfold logCharacter
    rw [<- Complex.exp_conj]
    congr 1
    simp
  rw [hConj]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem sum_range_succ_eq_Ioc {A : Type*} [AddCommMonoid A] (F : Nat -> A)
    (M : Nat) (hM : 1 <= M) :
    Finset.sum (Finset.range M) (fun n => F (n + 1)) =
      F 1 + Finset.sum (Finset.Ioc 1 M) F := by
  rw [<- Nat.Ico_zero_eq_range, Finset.sum_Ico_add', zero_add]
  have hSet : Finset.Ico 1 (M + 1) = insert 1 (Finset.Ioc 1 M) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hSet, Finset.sum_insert (by simp)]

theorem harmonicCharacterMean_zero_re (M : Nat) :
    (harmonicCharacterMean 0 M).re =
      Finset.sum (Finset.Ioc 1 M) (fun n : Nat => 1 / (n : Real)) / Real.log (M : Real) := by
  unfold harmonicCharacterMean
  rw [Complex.div_ofReal_re, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hZero : harmonicCharacter 0 (n : Real) = ((1 / (n : Real) : Real) : Complex) := by
    simp [harmonicCharacter, logCharacter]
  rw [hZero, Complex.ofReal_re]

/-- Logarithmic harmonic averaging discards every vanishing observation error. -/
theorem tendsto_harmonicWaveMean_zero (e : Nat -> Real)
    (he : Tendsto e atTop (nhds 0)) (w : Real) :
    Tendsto (harmonicWaveMean e w) atTop (nhds 0) := by
  let g : Nat -> Real := fun n => 1 / ((n + 1 : Nat) : Real)
  let f : Nat -> Complex := fun n =>
    (e (n + 1) : Complex) * logCharacter (-(4 * w)) ((n + 1 : Nat) : Real) /
      (((n + 1 : Nat) : Real) : Complex)
  have hLog : Tendsto (fun M : Nat => Real.log (M : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLogNe : Filter.Eventually (fun M : Nat => Not (Real.log (M : Real) = 0)) atTop := by
    filter_upwards [eventually_ge_atTop (2 : Nat)] with M hM
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < M by omega)))
  have hGMean : Tendsto (fun M : Nat =>
      Finset.sum (Finset.range M) g / Real.log (M : Real)) atTop (nhds 1) := by
    have hH : Tendsto (fun M : Nat => (harmonicCharacterMean 0 M).re) atTop (nhds 1) := by
      simpa only [harmonicCharacterMean, Function.comp_def, Complex.one_re] using
        (Complex.continuous_re.tendsto (1 : Complex)).comp tendsto_harmonicCharacter_mean_zero
    have hInv : Tendsto (fun M : Nat => 1 / Real.log (M : Real)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hLog
    have h := hInv.add hH
    norm_num only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : Nat)] with M hM
    rw [harmonicCharacterMean_zero_re]
    dsimp only [g]
    rw [sum_range_succ_eq_Ioc (fun n : Nat => 1 / (n : Real)) M hM]
    norm_num only [Nat.cast_one, div_one]
    rw [add_div]
  have hGBig : Asymptotics.IsBigO atTop
      (fun M : Nat => Finset.sum (Finset.range M) g)
      (fun M : Nat => Real.log (M : Real)) :=
    Asymptotics.isBigO_of_div_tendsto_nhds
      (hLogNe.mono (fun M hM h => (hM h).elim)) 1 hGMean
  have hLittle : Asymptotics.IsLittleO atTop f g := by
    apply Asymptotics.isLittleO_iff.mpr
    intro eps heps
    have hSmall : Filter.Eventually (fun n : Nat => norm (e (n + 1)) <= eps) atTop := by
      have h := ((he.comp (tendsto_add_atTop_nat 1)).norm).eventually
        (eventually_le_nhds (by simpa only [norm_zero] using heps))
      exact h
    filter_upwards [hSmall] with n hn
    have hnp : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
    dsimp only [f, g]
    simp only [norm_div, norm_mul, norm_logCharacter, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnp, abs_div, abs_one]
    have h := div_le_div_of_nonneg_right hn hnp.le
    simpa only [div_eq_mul_inv, one_mul, Real.norm_eq_abs] using h
  have hSum := hLittle.sum_range
    (fun n => by dsimp [g]; positivity)
    (by simpa only [g, Nat.cast_add, Nat.cast_one] using
      Real.tendsto_sum_range_one_div_nat_succ_atTop)
  have hRaw := hSum.trans_isBigO hGBig
  have hComplex : Asymptotics.IsLittleO atTop
      (fun M : Nat => Finset.sum (Finset.range M) f)
      (fun M : Nat => (Real.log (M : Real) : Complex)) := by
    apply Asymptotics.IsLittleO.of_norm_right
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hRaw.norm_right
  have hZero : Tendsto (fun M : Nat =>
      Finset.sum (Finset.range M) f / (Real.log (M : Real) : Complex))
      atTop (nhds 0) := by
    apply (Asymptotics.isLittleO_iff_tendsto' ?_).mp hComplex
    filter_upwards [hLogNe] with M hM h
    exact (hM (Complex.ofReal_eq_zero.mp h)).elim
  have hOneR : Tendsto (fun M : Nat => e 1 / Real.log (M : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hLog
  have hOne : Tendsto (fun M : Nat => (e 1 : Complex) / (Real.log (M : Real) : Complex))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_div] using
      (Complex.continuous_ofReal.tendsto (0 : Real)).comp hOneR
  have h := hZero.sub hOne
  norm_num only [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with M hM
  dsimp only [f]
  have hShift := sum_range_succ_eq_Ioc
    (fun n : Nat => (e n : Complex) * logCharacter (-(4 * w)) (n : Real) /
      ((n : Real) : Complex)) M hM
  rw [hShift]
  simp only [Nat.cast_one, logCharacter, Real.log_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one, Complex.ofReal_one, div_one]
  simp only [harmonicWaveMean, logCharacter, Complex.logCharacter]
  push_cast
  ring

theorem harmonicWaveMean_sub (g h : Nat -> Real) (w : Real) (M : Nat) :
    harmonicWaveMean (fun n => g n - h n) w M =
      harmonicWaveMean g w M - harmonicWaveMean h w M := by
  unfold harmonicWaveMean
  simp only [Complex.ofReal_sub, sub_mul, sub_div, Finset.sum_sub_distrib]

namespace QuadraticPrimeLaw

/- The critical-line multiplicity reconstruction theorem has its canonical
maintained owner in Helpers.XiZeroMultiplicity. -/
end QuadraticPrimeLaw

end PrimeFactorOscillations
