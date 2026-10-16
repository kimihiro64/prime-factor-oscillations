/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.Fourier.LogarithmicCharacter

/-!
# Absolutely summable logarithmic spectra

Harmonic Fourier extraction is valid for every absolutely summable complex spectrum.
Real spectra split into their positive and negative frequency parts.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Complex

theorem tendsto_tsum_harmonicCharacterMean {J : Type*}
    (a : J -> Complex) (f : J -> Real) (ha : Summable (fun j : J => norm (a j))) :
    Tendsto (fun N : Nat => tsum (fun j : J => a j * harmonicCharacterMean (f j) N))
      atTop (nhds (tsum (fun j : J => if f j = 0 then a j else 0))) := by
  classical
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun j : J => 2 * norm (a j)) (ha.mul_left 2) ?_ ?_
  . intro j
    have hConst : Tendsto (fun _ : Nat => a j) atTop (nhds (a j)) := tendsto_const_nhds
    have h := hConst.mul (tendsto_harmonicCharacter_mean (f j))
    change Tendsto (fun N : Nat => a j * harmonicCharacterMean (f j) N) atTop
      (nhds (a j * (if f j = 0 then 1 else 0))) at h
    simpa only [mul_ite, mul_one, mul_zero] using h
  . filter_upwards [eventually_norm_harmonicCharacterMean_le_two] with N hN
    intro j
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_left (hN (f j)) (norm_nonneg (a j))
    simpa only [mul_comm] using h

theorem logCharacter_sub (v w x : Real) :
    logCharacter (v - w) x = logCharacter v x * logCharacter (-w) x := by
  unfold logCharacter
  rw [<- Complex.exp_add]
  congr 1 <;> push_cast <;> ring

def logSpectrum {J : Type*} (a : J -> Complex) (f : J -> Real) (x : Real) : Complex :=
  tsum (fun j : J => a j * logCharacter (f j) x)

theorem summable_logSpectrum {J : Type*} (a : J -> Complex) (f : J -> Real)
    (ha : Summable (fun j : J => norm (a j))) (x : Real) :
    Summable (fun j : J => a j * logCharacter (f j) x) := by
  apply ha.of_norm_bounded
  intro j
  rw [norm_mul, norm_logCharacter, mul_one]

def harmonicSpectrumMean {J : Type*} (a : J -> Complex) (f : J -> Real)
    (w : Real) (N : Nat) : Complex :=
  Finset.sum (Finset.Ioc 1 N) (fun n : Nat =>
    logSpectrum a f (n : Real) * logCharacter (-w) (n : Real) / (n : Complex)) /
      (Real.log (N : Real) : Complex)

theorem harmonicSpectrumMean_eq_tsum {J : Type*} (a : J -> Complex) (f : J -> Real)
    (ha : Summable (fun j : J => norm (a j))) (w : Real) (N : Nat) :
    harmonicSpectrumMean a f w N =
      tsum (fun j : J => a j * harmonicCharacterMean (f j - w) N) := by
  have hS : forall n : Nat,
      Summable (fun j : J => a j * harmonicCharacter (f j - w) (n : Real)) := by
    intro n
    have h := (summable_logSpectrum a (fun j : J => f j - w) ha (n : Real)).div_const
      (n : Complex)
    convert h using 1
    funext j
    dsimp only [harmonicCharacter]
    push_cast
    ring
  have hTerm : forall n : Nat,
      logSpectrum a f (n : Real) * logCharacter (-w) (n : Real) / (n : Complex) =
      tsum (fun j : J => a j * harmonicCharacter (f j - w) (n : Real)) := by
    intro n
    unfold logSpectrum
    rw [<- tsum_mul_right, <- tsum_div_const]
    apply tsum_congr
    intro j
    dsimp only [harmonicCharacter]
    rw [logCharacter_sub]
    push_cast
    ring
  have hSwap := Summable.tsum_finsetSum (s := Finset.Ioc (1 : Nat) N)
    (f := fun (n : Nat) (j : J) => a j * harmonicCharacter (f j - w) (n : Real))
    (fun n _ => hS n)
  calc
    harmonicSpectrumMean a f w N =
        tsum (fun j : J => Finset.sum (Finset.Ioc 1 N)
          (fun n : Nat => a j * harmonicCharacter (f j - w) (n : Real))) /
            (Real.log (N : Real) : Complex) := by
      unfold harmonicSpectrumMean
      simp_rw [hTerm]
      rw [<- hSwap]
    _ = _ := by
      rw [<- tsum_div_const]
      apply tsum_congr
      intro j
      unfold harmonicCharacterMean
      rw [<- Finset.mul_sum, mul_div_assoc]

/-- Finite harmonic observations recover each frequency fiber of an arbitrary
absolutely summable logarithmic spectrum. -/
theorem tendsto_harmonicSpectrumMean {J : Type*}
    (a : J -> Complex) (f : J -> Real) (ha : Summable (fun j : J => norm (a j))) (w : Real) :
    Tendsto (harmonicSpectrumMean a f w) atTop
      (nhds (tsum (fun j : J => if f j = w then a j else 0))) := by
  have hId : harmonicSpectrumMean a f w =
      (fun N : Nat => tsum (fun j : J => a j * harmonicCharacterMean (f j - w) N)) :=
    funext (fun N => harmonicSpectrumMean_eq_tsum a f ha w N)
  rw [hId]
  simpa only [sub_eq_zero] using
    tendsto_tsum_harmonicCharacterMean a (fun j : J => f j - w) ha


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


end Complex
