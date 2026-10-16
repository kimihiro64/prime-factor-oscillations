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
import PrimeFactorOscillations.Helpers.XiZeroMultiplicity
import PrimeFactorOscillations.Mathlib.Analysis.Fourier.LogarithmicSpectrum
import PrimeFactorOscillations.Mathlib.Analysis.Fourier.LogarithmicStability

/-!
# Zero-frequency recovery from probability ratios

The completed xi formula is an absolutely summable logarithmic spectrum. Quartic harmonic observation recovers every frequency fiber.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations

open Robin1984 Complex

def xiWaveWeight (p : RiemannXiDivisorZeroIndex) : Real :=
  1 / (1 / 4 + (riemannXiDivisorZeroValue p).im ^ 2)

theorem xiWaveWeight_nonneg (p : RiemannXiDivisorZeroIndex) :
    0 <= xiWaveWeight p := by
  unfold xiWaveWeight
  positivity

theorem xiWaveWeight_eq_norm (hRH : RiemannHypothesis) (p : RiemannXiDivisorZeroIndex) :
    xiWaveWeight p = (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ 2 := by
  unfold xiWaveWeight
  rw [inv_pow, Complex.sq_norm, Complex.normSq_apply,
    riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p]
  congr 1 <;> ring

theorem xiZeroDenominator_eq (hRH : RiemannHypothesis) (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p) =
      ((1 / 4 + (riemannXiDivisorZeroValue p).im ^ 2 : Real) : Complex) := by
  have hr := riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
  push_cast
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pow_two, hr] <;> ring

theorem summable_xiWaveWeight (hRH : RiemannHypothesis) :
    Summable (fun p : RiemannXiDivisorZeroIndex => xiWaveWeight p) := by
  simpa only [xiWaveWeight_eq_norm hRH] using summable_robinXiZeroWeight

theorem summable_norm_xiWaveCoefficient (hRH : RiemannHypothesis) :
    Summable (fun p : RiemannXiDivisorZeroIndex => norm ((xiWaveWeight p : Real) : Complex)) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (xiWaveWeight_nonneg _)] using
    summable_xiWaveWeight hRH

theorem nicolasZeroWave_eq_logSpectrum (hRH : RiemannHypothesis)
    {x : Real} (hx : 1 < x) :
    nicolasZeroWave x =
      (logSpectrum (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p : Complex))
        (fun p => (riemannXiDivisorZeroValue p).im) x).re := by
  rw [nicolasZeroWave_eq_spectral_sum hRH hx]
  congr 1
  apply tsum_congr
  intro p
  rw [cpow_im_eq_logCharacter _ (zero_lt_one.trans hx), xiZeroDenominator_eq hRH p]
  simp only [xiWaveWeight, Complex.ofReal_div, Complex.ofReal_one]
  ring

theorem ofReal_nicolasZeroWave_fourthPower (hRH : RiemannHypothesis)
    {n : Nat} (hn : 1 < n) :
    (nicolasZeroWave ((n : Real) ^ 4) : Complex) =
      (logSpectrum (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p : Complex))
          (fun p => 4 * (riemannXiDivisorZeroValue p).im) (n : Real) +
        logSpectrum (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p : Complex))
          (fun p => -(4 * (riemannXiDivisorZeroValue p).im)) (n : Real)) / 2 := by
  have hnR : (1 : Real) < n := by exact_mod_cast hn
  have hx : (1 : Real) < (n : Real) ^ 4 := by nlinarith [sq_nonneg ((n : Real) ^ 2 - 1)]
  rw [nicolasZeroWave_eq_logSpectrum hRH hx,
    ofReal_re_logSpectrum _ _ (summable_norm_xiWaveCoefficient hRH)]
  congr 1 <;> congr 1 <;> apply tsum_congr <;> intro p <;> rw [logCharacter_pow] <;>
    norm_num <;> congr 2 <;> ring

theorem tsum_xiWaveWeight_frequency (hRH : RiemannHypothesis) (w : Real) :
    tsum (fun p : RiemannXiDivisorZeroIndex =>
      if (riemannXiDivisorZeroValue p).im = w then (xiWaveWeight p : Complex) else 0) =
        (xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I) : Complex) /
          ((1 / 4 + w ^ 2 : Real) : Complex) := by
  classical
  have hTerm : (fun p : RiemannXiDivisorZeroIndex =>
      if (riemannXiDivisorZeroValue p).im = w then (xiWaveWeight p : Complex) else 0) =
      (fun p : RiemannXiDivisorZeroIndex =>
        if (riemannXiDivisorZeroValue p).im = w
        then ((1 / (1 / 4 + w ^ 2) : Real) : Complex) else 0) := by
    funext p
    by_cases hp : (riemannXiDivisorZeroValue p).im = w <;> simp [hp, xiWaveWeight]
  rw [hTerm, tsum_xiZeroFrequencyFiber_const hRH w]
  push_cast
  ring

def xiFrequencyCoefficient (w : Real) : Complex :=
  (xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I) : Complex) /
    ((1 / 4 + w ^ 2 : Real) : Complex)

theorem xiFrequencyCoefficient_neg (w : Real) :
    xiFrequencyCoefficient (-w) = xiFrequencyCoefficient w := by
  unfold xiFrequencyCoefficient
  rw [xiZeroMultiplicity_frequency_neg]
  simp

theorem tendsto_xi_harmonicSpectrumMean (hRH : RiemannHypothesis) (w : Real) :
    Tendsto
      (harmonicSpectrumMean (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p : Complex))
        (fun p => 4 * (riemannXiDivisorZeroValue p).im) (4 * w))
      atTop (nhds (xiFrequencyCoefficient w)) := by
  have h := tendsto_harmonicSpectrumMean
    (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p : Complex))
    (fun p => 4 * (riemannXiDivisorZeroValue p).im)
    (summable_norm_xiWaveCoefficient hRH) (4 * w)
  have hLimit : tsum (fun p : RiemannXiDivisorZeroIndex =>
      if 4 * (riemannXiDivisorZeroValue p).im = 4 * w then (xiWaveWeight p : Complex) else 0) =
      xiFrequencyCoefficient w := by
    calc
      _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
          if (riemannXiDivisorZeroValue p).im = w then (xiWaveWeight p : Complex) else 0) := by
        apply tsum_congr
        intro p
        have he : 4 * (riemannXiDivisorZeroValue p).im = 4 * w <->
            (riemannXiDivisorZeroValue p).im = w := by constructor <;> intro hp <;> linarith
        simp only [he]
      _ = _ := tsum_xiWaveWeight_frequency hRH w
  rwa [hLimit] at h

theorem tendsto_xi_harmonicSpectrumMean_neg (hRH : RiemannHypothesis) (w : Real) :
    Tendsto
      (harmonicSpectrumMean (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p : Complex))
        (fun p => -(4 * (riemannXiDivisorZeroValue p).im)) (4 * w))
      atTop (nhds (xiFrequencyCoefficient w)) := by
  have h := tendsto_harmonicSpectrumMean
    (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p : Complex))
    (fun p => -(4 * (riemannXiDivisorZeroValue p).im))
    (summable_norm_xiWaveCoefficient hRH) (4 * w)
  have hLimit : tsum (fun p : RiemannXiDivisorZeroIndex =>
      if -(4 * (riemannXiDivisorZeroValue p).im) = 4 * w
      then (xiWaveWeight p : Complex) else 0) = xiFrequencyCoefficient w := by
    calc
      _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
          if (riemannXiDivisorZeroValue p).im = -w then (xiWaveWeight p : Complex) else 0) := by
        apply tsum_congr
        intro p
        have he : -(4 * (riemannXiDivisorZeroValue p).im) = 4 * w <->
            (riemannXiDivisorZeroValue p).im = -w := by constructor <;> intro hp <;> linarith
        simp only [he]
      _ = xiFrequencyCoefficient (-w) := tsum_xiWaveWeight_frequency hRH (-w)
      _ = _ := xiFrequencyCoefficient_neg w
  rwa [hLimit] at h

def harmonicWaveMean (g : Nat -> Real) (w : Real) (M : Nat) : Complex :=
  Finset.sum (Finset.Ioc 1 M) (fun n : Nat =>
    (g n : Complex) * logCharacter (-(4 * w)) (n : Real) / (n : Complex)) /
      (Real.log (M : Real) : Complex)

theorem harmonicWaveMean_nicolas_eq (hRH : RiemannHypothesis) (w : Real) (M : Nat) :
    harmonicWaveMean (fun n => nicolasZeroWave ((n : Real) ^ 4)) w M =
      (harmonicSpectrumMean (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p : Complex))
          (fun p => 4 * (riemannXiDivisorZeroValue p).im) (4 * w) M +
        harmonicSpectrumMean (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p : Complex))
          (fun p => -(4 * (riemannXiDivisorZeroValue p).im)) (4 * w) M) / 2 := by
  unfold harmonicWaveMean harmonicSpectrumMean
  rw [<- add_div, <- Finset.sum_add_distrib, div_div, mul_comm _ (2 : Complex), <- div_div]
  conv_rhs => rw [Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 < n := (Finset.mem_Ioc.mp hn).1
  rw [ofReal_nicolasZeroWave_fourthPower hRH hn1]
  ring

theorem tendsto_harmonicWaveMean_nicolas (hRH : RiemannHypothesis) (w : Real) :
    Tendsto (harmonicWaveMean (fun n => nicolasZeroWave ((n : Real) ^ 4)) w)
      atTop (nhds (xiFrequencyCoefficient w)) := by
  have h := ((tendsto_xi_harmonicSpectrumMean hRH w).add
    (tendsto_xi_harmonicSpectrumMean_neg hRH w)).div_const (2 : Complex)
  have hId : harmonicWaveMean (fun n => nicolasZeroWave ((n : Real) ^ 4)) w =
      (fun M =>
        (harmonicSpectrumMean (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p : Complex))
            (fun p => 4 * (riemannXiDivisorZeroValue p).im) (4 * w) M +
          harmonicSpectrumMean (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p : Complex))
            (fun p => -(4 * (riemannXiDivisorZeroValue p).im)) (4 * w) M) / 2) :=
    funext (harmonicWaveMean_nicolas_eq hRH w)
  rw [hId]
  convert h using 1 <;> first | rfl | ring

/-- Vanishing observation errors preserve the quartic coefficient. -/
theorem tendsto_harmonicWaveMean_of_sub {g h : Nat -> Real} (w : Real) {c : Complex}
    (hError : Tendsto (fun n => g n - h n) atTop (nhds 0))
    (hMean : Tendsto (harmonicWaveMean h w) atTop (nhds c)) :
    Tendsto (harmonicWaveMean g w) atTop (nhds c) := by
  exact Complex.tendsto_harmonicLogMean_of_sub (4 * w) hError hMean

namespace QuadraticPrimeLaw

/-- One admissible counting family sampled only at fourth powers determines
every critical-line xi-zero multiplicity by harmonic Fourier observations. -/
theorem tendsto_harmonicWaveMean_normalizedFloorRatioWave
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (hRH : RiemannHypothesis) (w : Real) :
    Tendsto
      (harmonicWaveMean (fun n : Nat => law.normalizedFloorRatioWave alpha (n ^ 4)) w)
      atTop (nhds (xiFrequencyCoefficient w)) := by
  apply tendsto_harmonicWaveMean_of_sub w ?_ (tendsto_harmonicWaveMean_nicolas hRH w)
  have h := (law.tendsto_normalizedFloorRatioWave_sub_zeroWave alpha ha hRH).comp
    Nat.strictMono_fourthPower.tendsto_atTop
  simpa only [Function.comp_def, Nat.cast_pow] using h

/-- Deleting or changing finitely many observations leaves zero recovery intact. -/
theorem tendsto_harmonicWaveMean_eventuallyEq_normalizedFloorRatioWave
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (hRH : RiemannHypothesis) (w : Real) (g : Nat -> Real)
    (hg : Filter.EventuallyEq atTop g
      (fun n : Nat => law.normalizedFloorRatioWave alpha (n ^ 4))) :
    Tendsto (harmonicWaveMean g w) atTop (nhds (xiFrequencyCoefficient w)) := by
  apply tendsto_harmonicWaveMean_of_sub w ?_
    (law.tendsto_harmonicWaveMean_normalizedFloorRatioWave alpha ha hRH w)
  apply tendsto_const_nhds.congr'
  filter_upwards [hg] with n hn
  rw [hn, sub_self]

/-- Failure of RH forces arbitrarily late arbitrarily negative observations
on every admissible sparse mesh. -/
theorem frequently_normalizedFloorRatioWave_lt_of_not_RH
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (u : Nat -> Nat) (hu : StrictMono u)
    (hmesh : Nat.SubpowerGapBound u (3 / 4 : Real))
    (hNotRH : Not RiemannHypothesis) (A : Real) :
    Filter.Frequently (fun j : Nat => law.normalizedFloorRatioWave alpha (u j) < A) atTop := by
  have hNotBound : Not (Exists (fun B : Real =>
      Filter.Eventually (fun j : Nat => B <= law.normalizedFloorRatioWave alpha (u j)) atTop)) := by
    intro h
    exact hNotRH ((law.riemannHypothesis_iff_subpower_mesh_normalizedFloorRatioWave_bounded_below
      alpha ha u hu hmesh).mpr h)
  change Not (Filter.Eventually (fun j : Nat =>
    Not (law.normalizedFloorRatioWave alpha (u j) < A)) atTop)
  intro h
  apply hNotBound
  refine Exists.intro A ?_
  filter_upwards [h] with j hj
  exact le_of_not_gt hj

end QuadraticPrimeLaw

end PrimeFactorOscillations
