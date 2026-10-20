/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.XiZeroLogSpectrum
import PrimeFactorOscillations.Helpers.XiZetaMultiplicity
import PrimeFactorOscillations.Mathlib.Analysis.Fourier.LogarithmicBilinear

/-!
# Universal logarithmic second moments

Under RH, two fixed quadratic prime laws have the same full second moment.
Multiplicity collisions are retained. This is not a zero-exclusion estimate.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations

open Robin1984 Complex

def xiVarianceBudget : Real :=
  tsum (fun p : RiemannXiDivisorZeroIndex =>
    xiWaveWeight p *
      ((xiZeroMultiplicity ((1 / 2 : Complex) +
        ((riemannXiDivisorZeroValue p).im : Complex) * Complex.I) : Nat) : Real) *
          xiWaveWeight p)

def signedXiFrequency (positive : Bool) (p : RiemannXiDivisorZeroIndex) : Real :=
  if positive then 4 * (riemannXiDivisorZeroValue p).im
  else -(4 * (riemannXiDivisorZeroValue p).im)

set_option maxRecDepth 100 in
theorem xi_pair_resonance (hRH : RiemannHypothesis) (u v : Bool) :
    tsum (fun p : Prod RiemannXiDivisorZeroIndex RiemannXiDivisorZeroIndex =>
      if signedXiFrequency u p.1 + signedXiFrequency v p.2 = 0
      then (xiWaveWeight p.1 : Complex) * (xiWaveWeight p.2 : Complex) else 0) =
        (xiVarianceBudget : Complex) := by
  classical
  let a : RiemannXiDivisorZeroIndex -> Complex := fun p => (xiWaveWeight p : Complex)
  have hn := summable_norm_xiWaveCoefficient hRH
  have hs : Summable (fun p : Prod RiemannXiDivisorZeroIndex RiemannXiDivisorZeroIndex =>
      if signedXiFrequency u p.1 + signedXiFrequency v p.2 = 0
      then a p.1 * a p.2 else 0) :=
    (summable_mul_of_summable_norm hn hn).norm.of_norm_bounded
      (fun p => by split_ifs <;> simp [a] <;> positivity)
  rw [hs.tsum_prod]
  have hrow : forall p : RiemannXiDivisorZeroIndex,
      tsum (fun q : RiemannXiDivisorZeroIndex =>
        if signedXiFrequency u p + signedXiFrequency v q = 0
        then a p * a q else 0) =
      (xiWaveWeight p : Complex) *
        xiFrequencyCoefficient (riemannXiDivisorZeroValue p).im := by
    intro p
    let w : Real := if u = v then -(riemannXiDivisorZeroValue p).im
      else (riemannXiDivisorZeroValue p).im
    have hw : forall q : RiemannXiDivisorZeroIndex,
        signedXiFrequency u p + signedXiFrequency v q = 0 <->
          (riemannXiDivisorZeroValue q).im = w := by
      intro q
      cases u <;> cases v <;>
        simp only [signedXiFrequency, w, Bool.false_eq_true, Bool.true_eq_false,
          ite_false, ite_true] <;>
        constructor <;> intro h <;> linarith
    have hc : xiFrequencyCoefficient w =
        xiFrequencyCoefficient (riemannXiDivisorZeroValue p).im := by
      dsimp only [w]
      split_ifs
      . exact xiFrequencyCoefficient_neg _
      . rfl
    simp_rw [hw]
    calc
      _ = a p * tsum (fun q : RiemannXiDivisorZeroIndex =>
          if (riemannXiDivisorZeroValue q).im = w then a q else 0) := by
        rw [<- tsum_mul_left]
        apply tsum_congr
        intro q
        split_ifs <;> simp
      _ = _ := by
        rw [tsum_xiWaveWeight_frequency hRH w]
        change (xiWaveWeight p : Complex) * xiFrequencyCoefficient w = _
        rw [hc]
  simp_rw [hrow]
  have hn2 : Summable (fun p : RiemannXiDivisorZeroIndex =>
      (xiWaveWeight p : Complex) *
        xiFrequencyCoefficient (riemannXiDivisorZeroValue p).im) := by
    simpa only [hrow] using hs.prod
  have hid : forall p : RiemannXiDivisorZeroIndex,
      (xiWaveWeight p : Complex) *
          xiFrequencyCoefficient (riemannXiDivisorZeroValue p).im =
        ((xiWaveWeight p *
          (xiZeroMultiplicity ((1 / 2 : Complex) +
            ((riemannXiDivisorZeroValue p).im : Complex) * Complex.I) : Real) *
              xiWaveWeight p : Real) : Complex) := by
    intro p
    simp only [xiFrequencyCoefficient, xiWaveWeight, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    ring
  have hr : Summable (fun p : RiemannXiDivisorZeroIndex =>
      xiWaveWeight p *
        (xiZeroMultiplicity ((1 / 2 : Complex) +
          ((riemannXiDivisorZeroValue p).im : Complex) * Complex.I) : Real) *
            xiWaveWeight p) := by
    apply hn2.norm.of_norm_bounded
    intro p
    rw [hid, Complex.norm_real]
  simp_rw [hid]
  exact (Complex.ofRealCLM.map_tsum hr).symm


theorem harmonicSquareMean_nicolas_eq (hRH : RiemannHypothesis) (N : Nat) :
    harmonicWaveMean (fun n => (nicolasZeroWave ((n : Real) ^ 4)) ^ 2) 0 N =
      (harmonicBilinearMean (fun p => (xiWaveWeight p : Complex))
          (signedXiFrequency true) (fun p => (xiWaveWeight p : Complex))
          (signedXiFrequency true) N +
        harmonicBilinearMean (fun p => (xiWaveWeight p : Complex))
          (signedXiFrequency true) (fun p => (xiWaveWeight p : Complex))
          (signedXiFrequency false) N +
        harmonicBilinearMean (fun p => (xiWaveWeight p : Complex))
          (signedXiFrequency false) (fun p => (xiWaveWeight p : Complex))
          (signedXiFrequency true) N +
        harmonicBilinearMean (fun p => (xiWaveWeight p : Complex))
          (signedXiFrequency false) (fun p => (xiWaveWeight p : Complex))
          (signedXiFrequency false) N) / 4 := by
  unfold harmonicWaveMean harmonicBilinearMean
  simp only [neg_zero, logCharacter, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one, Complex.ofReal_pow]
  rw [<- add_div, <- add_div, <- add_div, div_right_comm]
  apply congrArg (fun z : Complex => z / (Real.log (N : Real) : Complex))
  rw [<- Finset.sum_add_distrib, <- Finset.sum_add_distrib,
    <- Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 < n := (Finset.mem_Ioc.mp hn).1
  rw [ofReal_nicolasZeroWave_fourthPower hRH hn1]
  have hp : signedXiFrequency true =
      (fun p => 4 * (riemannXiDivisorZeroValue p).im) := by funext p; rfl
  have hm : signedXiFrequency false =
      (fun p => -(4 * (riemannXiDivisorZeroValue p).im)) := by funext p; rfl
  rw [hp, hm]
  norm_num
  ring

/-- The entire second moment, including all multiplicity collisions. -/
theorem tendsto_harmonicSquareMean_nicolas (hRH : RiemannHypothesis) :
    Tendsto
      (harmonicWaveMean (fun n => (nicolasZeroWave ((n : Real) ^ 4)) ^ 2) 0)
      atTop (nhds (xiVarianceBudget : Complex)) := by
  have ht : forall u v : Bool,
      Tendsto
        (harmonicBilinearMean (fun p => (xiWaveWeight p : Complex))
          (signedXiFrequency u) (fun p => (xiWaveWeight p : Complex))
          (signedXiFrequency v))
        atTop (nhds (xiVarianceBudget : Complex)) := by
    intro u v
    have h := tendsto_harmonicBilinearMean
      (fun p => (xiWaveWeight p : Complex)) (signedXiFrequency u)
      (fun p => (xiWaveWeight p : Complex)) (signedXiFrequency v)
      (summable_norm_xiWaveCoefficient hRH) (summable_norm_xiWaveCoefficient hRH)
    rw [xi_pair_resonance hRH u v] at h
    exact h
  have h := (((ht true true).add (ht true false)).add (ht false true)).add
    (ht false false)
  have hh := h.div_const (4 : Complex)
  have hc : ((xiVarianceBudget : Complex) + xiVarianceBudget +
      xiVarianceBudget + xiVarianceBudget) / 4 = xiVarianceBudget := by ring
  rw [hc] at hh
  exact hh.congr' (Filter.Eventually.of_forall
    (fun N => (harmonicSquareMean_nicolas_eq hRH N).symm))



namespace QuadraticPrimeLaw

/-- Any two admissible laws have the same entire logarithmic second moment. -/
theorem tendsto_harmonic_product_normalizedFloorRatioWave
    (law law' : QuadraticPrimeLaw) (alpha alpha' : Real)
    (ha : 0 < alpha) (ha' : 0 < alpha') (hRH : RiemannHypothesis) :
    Tendsto
      (harmonicWaveMean (fun n =>
        law.normalizedFloorRatioWave alpha (n ^ 4) *
          law'.normalizedFloorRatioWave alpha' (n ^ 4)) 0)
      atTop (nhds (xiVarianceBudget : Complex)) := by
  apply tendsto_harmonicWaveMean_of_sub 0 ?_ (tendsto_harmonicSquareMean_nicolas hRH)
  have hg := (law.tendsto_normalizedFloorRatioWave_sub_zeroWave alpha ha hRH).comp
    Nat.strictMono_fourthPower.tendsto_atTop
  have hh := (law'.tendsto_normalizedFloorRatioWave_sub_zeroWave alpha' ha' hRH).comp
    Nat.strictMono_fourthPower.tendsto_atTop
  simp only [Function.comp_def, Nat.cast_pow] at hg hh
  let B := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  have hB : 0 <= B :=
    (abs_nonneg _).trans (abs_nicolasZeroWave_le hRH (show (1 : Real) < 2 by norm_num))
  apply Filter.tendsto_product_sub_square hB ?_ hg hh
  filter_upwards [eventually_ge_atTop (2 : Nat)] with n hn
  have hnR : (2 : Real) <= n := by exact_mod_cast hn
  apply abs_nicolasZeroWave_le hRH
  nlinarith [sq_nonneg ((n : Real) ^ 2 - 1)]

end QuadraticPrimeLaw


theorem harmonicWaveMean_zero_re (g : Nat -> Real) (N : Nat) :
    (harmonicWaveMean g 0 N).re =
      Finset.sum (Finset.Ioc 1 N) (fun n : Nat => g n / (n : Real)) /
        Real.log (N : Real) := by
  unfold harmonicWaveMean
  simp only [mul_zero, neg_zero, logCharacter, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one]
  rw [Complex.div_ofReal_re, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact Complex.div_ofReal_re _ _

/-- A proved global bound, independent of any proposed zero-exclusion estimate. -/
theorem xiVarianceBudget_le (hRH : RiemannHypothesis) :
    xiVarianceBudget <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) ^ 2 := by
  let B := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  have hB : 0 <= B :=
    (abs_nonneg _).trans (abs_nicolasZeroWave_le hRH (show (1 : Real) < 2 by norm_num))
  have hleft := (Complex.continuous_re.tendsto (xiVarianceBudget : Complex)).comp
    (tendsto_harmonicSquareMean_nicolas hRH)
  have hright := ((Complex.continuous_re.tendsto (1 : Complex)).comp
    tendsto_harmonicCharacter_mean_zero).const_mul (B ^ 2)
  simp only [Function.comp_def, Complex.ofReal_re, Complex.one_re, mul_one] at hleft hright
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_ge_atTop (2 : Nat)] with N hN
  change (harmonicWaveMean (fun n => (nicolasZeroWave ((n : Real) ^ 4)) ^ 2) 0 N).re <=
    B ^ 2 * (harmonicCharacterMean 0 N).re
  rw [harmonicWaveMean_zero_re, harmonicCharacterMean_zero_re, <- mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (show 1 <= N by omega)))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 < n := (Finset.mem_Ioc.mp hn).1
  have hnR : (1 : Real) < n := by exact_mod_cast hn1
  have hx : (1 : Real) < (n : Real) ^ 4 := by
    nlinarith [sq_nonneg ((n : Real) ^ 2 - 1)]
  have hb := abs_nicolasZeroWave_le hRH hx
  change abs (nicolasZeroWave ((n : Real) ^ 4)) <= B at hb
  have hs : (nicolasZeroWave ((n : Real) ^ 4)) ^ 2 <= B ^ 2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hb)
      (add_nonneg hB (abs_nonneg (nicolasZeroWave ((n : Real) ^ 4))))
    nlinarith only [hm, sq_abs (nicolasZeroWave ((n : Real) ^ 4))]
  simpa only [mul_one_div] using
    div_le_div_of_nonneg_right hs (zero_lt_one.trans hnR).le

end PrimeFactorOscillations
