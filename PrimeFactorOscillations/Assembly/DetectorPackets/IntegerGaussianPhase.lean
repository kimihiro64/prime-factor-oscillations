/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerGaussianMoment

/-!
# IntegerGaussianPhase

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

namespace PrimeFactorOscillations.IntegerGaussianPhase

open IntegerGaussianMoment

theorem pure_phase_sub_norm (b h : Real) :
    norm (Complex.exp (Complex.I * ((b + h : Real) : Complex)) -
      Complex.exp (Complex.I * (b : Complex))) <= abs h := by
  have hFactor :
      Complex.exp (Complex.I * ((b + h : Real) : Complex)) -
        Complex.exp (Complex.I * (b : Complex)) =
      Complex.exp (Complex.I * (b : Complex)) *
        (Complex.exp (Complex.I * (h : Complex)) - 1) := by
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  have hUnit : norm (Complex.exp (Complex.I * (b : Complex))) = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hFactor, norm_mul, hUnit, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  have hSin : abs (Real.sin (h / 2)) <= abs (h / 2) := Real.abs_sin_le_abs
  calc
    _ <= abs (2 : Real) * abs (h / 2) := mul_le_mul_of_nonneg_left hSin (abs_nonneg _)
    _ = abs h := by rw [abs_div]; norm_num; ring

def phaseError (a b h : Real) (n : Int) : Complex :=
  (Real.exp (-a * (n : Real) ^ 2) : Complex) *
    (Complex.exp (Complex.I * (((b + h) * (n : Real) ^ 2 : Real) : Complex)) -
      Complex.exp (Complex.I * ((b * (n : Real) ^ 2 : Real) : Complex)))

theorem phaseError_norm (a b h : Real) (n : Int) :
    norm (phaseError a b h n) <=
      abs h * ((n : Real) ^ 2 * Real.exp (-a * (n : Real) ^ 2)) := by
  have hPhase := pure_phase_sub_norm (b * (n : Real) ^ 2) (h * (n : Real) ^ 2)
  have hExpand : (b + h) * (n : Real) ^ 2 =
      b * (n : Real) ^ 2 + h * (n : Real) ^ 2 := by ring
  unfold phaseError
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), hExpand]
  calc
    _ <= Real.exp (-a * (n : Real) ^ 2) * abs (h * (n : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hPhase (Real.exp_pos _).le
    _ = _ := by rw [abs_mul, abs_of_nonneg (sq_nonneg (n : Real))]; ring

theorem gaussian_phase_error :
    exists C : Real, 0 < C /\ forall (a b h : Real), 0 < a ->
      Summable (phaseError a b h) /\
      norm (tsum (phaseError a b h)) <= C * abs h / a ^ 2 := by
  choose C hC hMoment using gaussian_second_moment
  refine Exists.intro C (And.intro hC ?_)
  intro a b h ha
  have hm := hMoment a ha
  have hMajorant : Summable
      (fun n : Int => abs h * ((n : Real) ^ 2 * Real.exp (-a * (n : Real) ^ 2))) :=
    Summable.mul_left (abs h) hm.1
  have hNorm : Summable (fun n : Int => norm (phaseError a b h n)) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (phaseError_norm a b h) hMajorant
  have hSum : Summable (phaseError a b h) :=
    Summable.of_norm_bounded hMajorant (phaseError_norm a b h)
  refine And.intro hSum ?_
  calc
    _ <= tsum (fun n : Int => norm (phaseError a b h n)) := norm_tsum_le_tsum_norm hNorm
    _ <= tsum (fun n : Int =>
        abs h * ((n : Real) ^ 2 * Real.exp (-a * (n : Real) ^ 2))) :=
      hNorm.tsum_le_tsum (phaseError_norm a b h) hMajorant
    _ = abs h * tsum (fun n : Int =>
        (n : Real) ^ 2 * Real.exp (-a * (n : Real) ^ 2)) := tsum_mul_left
    _ <= abs h * (C / a ^ 2) := mul_le_mul_of_nonneg_left hm.2 (abs_nonneg _)
    _ = C * abs h / a ^ 2 := by ring

end PrimeFactorOscillations.IntegerGaussianPhase

