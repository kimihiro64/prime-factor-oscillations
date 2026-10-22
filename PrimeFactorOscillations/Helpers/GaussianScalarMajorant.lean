/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit scalar majorants for the actual log-Gaussian Mellin kernel

These estimates certify convergence and interchange. They do not bound or
discard the signed zero contribution to the physical prime-error probe.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem abs_mul_gaussian_le (a u : Real) (ha : 0 < a) :
    abs u * Real.exp (-(a * u ^ 2)) <= 1 + 1 / a := by
  have hB : 0 <= 1 + 1 / a := by positivity
  have hs : abs u <= 1 + u ^ 2 := by
    have h := sq_nonneg (abs u - 1 / 2)
    have hsq := sq_abs u
    nlinarith only [h, hsq]
  have hid : (1 + 1 / a) * (1 + a * u ^ 2) =
      1 + u ^ 2 + a * u ^ 2 + 1 / a := by
    field_simp
    ring
  have hp : abs u <= (1 + 1 / a) * (1 + a * u ^ 2) := by
    rw [hid]
    have hn := mul_nonneg ha.le (sq_nonneg u)
    have hi : 0 <= 1 / a := div_nonneg (by norm_num) ha.le
    linarith only [hs, hn, hi]
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a * u ^ 2)) hB
  have he' : abs u <= (1 + 1 / a) * Real.exp (a * u ^ 2) := by
    nlinarith only [hp, he]
  calc
    abs u * Real.exp (-(a * u ^ 2)) <=
        ((1 + 1 / a) * Real.exp (a * u ^ 2)) * Real.exp (-(a * u ^ 2)) :=
      mul_le_mul_of_nonneg_right he' (Real.exp_pos _).le
    _ = 1 + 1 / a := by
      rw [mul_assoc, <- Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem linear_gaussian_le (a C u : Real) (ha : 0 < a) (hC : 0 <= C) :
    (C + abs u) * Real.exp (-(a * u ^ 2)) <= C + 1 + 1 / a := by
  have he : Real.exp (-(a * u ^ 2)) <= 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha.le (sq_nonneg u)))
  have hc := mul_le_mul_of_nonneg_left he hC
  have hu := abs_mul_gaussian_le a u ha
  nlinarith only [hc, hu]

end PrimeFactorOscillations.PrimeClassDeletion
