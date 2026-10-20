/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.Fourier.LogarithmicSpectrum

/-!
# Bilinear logarithmic means

Absolutely summable spectra retain every additive resonance in their product.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace Complex

theorem logCharacter_add (v w x : Real) :
    logCharacter (v + w) x = logCharacter v x * logCharacter w x := by
  unfold logCharacter
  rw [<- Complex.exp_add]
  congr 1 <;> push_cast <;> ring

theorem logSpectrum_mul {J K : Type*} (a : J -> Complex) (f : J -> Real)
    (b : K -> Complex) (g : K -> Real)
    (ha : Summable (fun j => norm (a j)))
    (hb : Summable (fun k => norm (b k))) (x : Real) :
    logSpectrum a f x * logSpectrum b g x =
      logSpectrum (fun p : Prod J K => a p.1 * b p.2)
        (fun p => f p.1 + g p.2) x := by
  have hs := summable_mul_of_summable_norm
    (summable_logSpectrum a f ha x).norm
    (summable_logSpectrum b g hb x).norm
  unfold logSpectrum
  rw [<- tsum_mul_right]
  calc
    _ = tsum (fun j => tsum (fun k =>
        (a j * logCharacter (f j) x) * (b k * logCharacter (g k) x))) := by
      apply tsum_congr
      intro j
      rw [tsum_mul_left]
    _ = tsum (fun p : Prod J K =>
        (a p.1 * logCharacter (f p.1) x) *
          (b p.2 * logCharacter (g p.2) x)) := hs.tsum_prod.symm
    _ = _ := by
      apply tsum_congr
      intro p
      rw [logCharacter_add]
      ring

def harmonicBilinearMean {J K : Type*} (a : J -> Complex) (f : J -> Real)
    (b : K -> Complex) (g : K -> Real) (N : Nat) : Complex :=
  Finset.sum (Finset.Ioc 1 N) (fun n : Nat =>
    logSpectrum a f (n : Real) * logSpectrum b g (n : Real) / (n : Complex)) /
      (Real.log (N : Real) : Complex)

/-- All additive resonances are retained, including repeated frequencies. -/
theorem tendsto_harmonicBilinearMean {J K : Type*}
    (a : J -> Complex) (f : J -> Real)
    (b : K -> Complex) (g : K -> Real)
    (ha : Summable (fun j => norm (a j)))
    (hb : Summable (fun k => norm (b k))) :
    Tendsto (harmonicBilinearMean a f b g) atTop
      (nhds (tsum (fun p : Prod J K =>
        if f p.1 + g p.2 = 0 then a p.1 * b p.2 else 0))) := by
  have hn := (summable_mul_of_summable_norm ha hb).norm
  have h := tendsto_harmonicSpectrumMean
    (fun p : Prod J K => a p.1 * b p.2) (fun p => f p.1 + g p.2) hn 0
  have he : harmonicBilinearMean a f b g =
      harmonicSpectrumMean (fun p : Prod J K => a p.1 * b p.2)
        (fun p => f p.1 + g p.2) 0 := by
    funext N
    unfold harmonicBilinearMean harmonicSpectrumMean
    apply congrArg (fun z : Complex => z / (Real.log (N : Real) : Complex))
    apply Finset.sum_congr rfl
    intro n hn
    simp only [neg_zero, logCharacter, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, mul_one]
    rw [logSpectrum_mul a f b g ha hb]
  rw [he]
  exact h

end Complex

namespace Filter

theorem tendsto_product_sub_square {g h w : Nat -> Real} {B : Real}
    (hB : 0 <= B) (hw : Filter.Eventually (fun n => abs (w n) <= B) atTop)
    (hg : Tendsto (fun n => g n - w n) atTop (nhds 0))
    (hh : Tendsto (fun n => h n - w n) atTop (nhds 0)) :
    Tendsto (fun n => g n * h n - (w n) ^ 2) atTop (nhds 0) := by
  have hga := hg.abs
  have hha := hh.abs
  have hu := (hga.mul hha).add ((hga.add hha).const_mul B)
  simp only [abs_zero, zero_mul, zero_add, mul_zero] at hu
  have hbound : Filter.Eventually (fun n =>
      abs (g n * h n - (w n) ^ 2) <=
        abs (g n - w n) * abs (h n - w n) +
          B * (abs (g n - w n) + abs (h n - w n))) atTop := by
    filter_upwards [hw] with n hn
    have he : g n * h n - (w n) ^ 2 =
        (g n - w n) * (h n - w n) +
          w n * ((g n - w n) + (h n - w n)) := by ring
    rw [he]
    calc
      _ <= abs ((g n - w n) * (h n - w n)) +
          abs (w n * ((g n - w n) + (h n - w n))) := abs_add_le _ _
      _ <= _ := by
        rw [abs_mul, abs_mul]
        exact _root_.add_le_add (le_refl _)
          (mul_le_mul hn (abs_add_le _ _) (abs_nonneg _) hB)
  have hz := squeeze_zero' (Filter.Eventually.of_forall
    (fun n => abs_nonneg (g n * h n - (w n) ^ 2))) hbound hu
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by
    simpa only [Real.norm_eq_abs] using hz)

end Filter
