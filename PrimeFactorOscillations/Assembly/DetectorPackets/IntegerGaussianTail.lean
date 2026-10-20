/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerGaussianMoment

/-!
# IntegerGaussianTail

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.IntegerGaussianTail

open IntegerGaussianMoment SchwartzFrequencyTail

theorem scalar_gaussian_tail (a x : Real) (ha : 0 < a) (hx : 0 < x) :
    Real.exp (-a * x ^ 2) <= (1 / a) * (1 / x ^ 2) := by
  have hOne : Real.exp (-1) <= 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp_of_le (show (-1 : Real) <= 0 by norm_num))
  have h := (Real.mul_exp_neg_le_exp_neg_one (a * x ^ 2)).trans hOne
  apply le_of_mul_le_mul_right _ (mul_pos ha (pow_pos hx 2))
  calc
    _ = (a * x ^ 2) * Real.exp (-(a * x ^ 2)) := by ring
    _ <= 1 := h
    _ = ((1 / a) * (1 / x ^ 2)) * (a * x ^ 2) := by field_simp

theorem reciprocal_square_sum :
    exists B : Real, 0 < B /\
      Summable (fun n : Int => 1 / (n.natAbs : Real) ^ 2) /\
      tsum (fun n : Int => 1 / (n.natAbs : Real) ^ 2) <= B := by
  choose B hB hFinite using finite_inverse_square_sum
  have hSum : Summable (fun n : Int => 1 / (n.natAbs : Real) ^ 2) :=
    summable_of_sum_le (fun n => by positivity) hFinite
  exact Exists.intro B (And.intro hB (And.intro hSum
    (le_of_tendsto hSum.hasSum (Filter.Eventually.of_forall hFinite))))

def offZeroTerm (a : Real) (phase : Int -> Real) (n : Int) : Complex :=
  if n = 0 then 0 else
    (Real.exp (-a * (n : Real) ^ 2) : Complex) *
      Complex.exp (Complex.I * (phase n : Complex))

def offZeroGaussian (a : Real) (phase : Int -> Real) : Complex :=
  tsum (offZeroTerm a phase)

theorem offZeroTerm_norm (a : Real) (ha : 0 < a) (phase : Int -> Real) (n : Int) :
    norm (offZeroTerm a phase n) <= (1 / a) * (1 / (n.natAbs : Real) ^ 2) := by
  by_cases hn : n = 0
  . subst n
    simp [offZeroTerm]
  . rw [offZeroTerm, ite_eq_right hn, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Real.exp_zero, mul_one]
    have hs : (n.natAbs : Real) ^ 2 = (n : Real) ^ 2 := by
      rw [natAbs_real, sq_abs]
    rw [<- hs]
    exact scalar_gaussian_tail a (n.natAbs : Real) ha
      (by exact_mod_cast (Int.natAbs_pos.mpr hn))

theorem offZeroGaussian_bound :
    exists C : Real, 0 < C /\ forall (a : Real) (phase : Int -> Real), 0 < a ->
      Summable (offZeroTerm a phase) /\ norm (offZeroGaussian a phase) <= C / a := by
  choose C hC hSum hBound using reciprocal_square_sum
  refine Exists.intro C (And.intro hC ?_)
  intro a phase ha
  have hMajorant : Summable (fun n : Int => (1 / a) * (1 / (n.natAbs : Real) ^ 2)) :=
    Summable.mul_left (1 / a) hSum
  have hNorm : Summable (fun n : Int => norm (offZeroTerm a phase n)) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (offZeroTerm_norm a ha phase) hMajorant
  refine And.intro (Summable.of_norm_bounded hMajorant (offZeroTerm_norm a ha phase)) ?_
  calc
    _ <= tsum (fun n : Int => norm (offZeroTerm a phase n)) := norm_tsum_le_tsum_norm hNorm
    _ <= tsum (fun n : Int => (1 / a) * (1 / (n.natAbs : Real) ^ 2)) :=
      hNorm.tsum_le_tsum (offZeroTerm_norm a ha phase) hMajorant
    _ = (1 / a) * tsum (fun n : Int => 1 / (n.natAbs : Real) ^ 2) := tsum_mul_left
    _ <= (1 / a) * C := mul_le_mul_of_nonneg_left hBound (by positivity)
    _ = C / a := by ring

end PrimeFactorOscillations.IntegerGaussianTail

