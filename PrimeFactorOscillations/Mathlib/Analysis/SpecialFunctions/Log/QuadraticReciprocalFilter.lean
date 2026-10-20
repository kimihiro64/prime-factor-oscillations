/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.PolynomialReciprocalTransport

/-!
# An explicit contracting quadratic on the reciprocal window

The polynomial has value one at zero and norm at most 25/217 on [1/2,4/3].
Its powers give square-filter errors at most 64 to the negative power, with
degree growing linearly in the power.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Polynomial

/-- The normalized shifted quadratic Chebyshev filter, written explicitly. -/
def reciprocalWindowQuadratic : Polynomial Real :=
  1 - Polynomial.C (528 / 217 : Real) * Polynomial.X +
    Polynomial.C (288 / 217 : Real) * Polynomial.X ^ 2

/-- The centering identity exposes the actual interval normalization. -/
theorem eval_reciprocalWindowQuadratic (x : Real) :
    Polynomial.eval x reciprocalWindowQuadratic =
      (2 * (12 * x - 11) ^ 2 - 25) / 217 := by
  simp only [reciprocalWindowQuadratic, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  ring

/-- Every power retains the normalization needed for a probability polynomial. -/
theorem eval_zero_reciprocalWindowQuadratic_pow (k : Nat) :
    Polynomial.eval 0 (reciprocalWindowQuadratic ^ k) = 1 := by
  rw [Polynomial.eval_pow, eval_reciprocalWindowQuadratic]
  norm_num

/-- The explicit filter has degree at most two. -/
theorem natDegree_reciprocalWindowQuadratic_le :
    reciprocalWindowQuadratic.natDegree <= 2 := by
  have hlin : (Polynomial.C (528 / 217 : Real) * Polynomial.X).natDegree <= 1 := by
    calc
      _ <= (Polynomial.C (528 / 217 : Real)).natDegree +
          (Polynomial.X : Polynomial Real).natDegree := Polynomial.natDegree_mul_le
      _ = 1 := by simp
  have hquad : (Polynomial.C (288 / 217 : Real) * Polynomial.X ^ 2).natDegree <= 2 := by
    calc
      _ <= (Polynomial.C (288 / 217 : Real)).natDegree +
          ((Polynomial.X : Polynomial Real) ^ 2).natDegree := Polynomial.natDegree_mul_le
      _ = 2 := by simp
  have hleft : (1 - Polynomial.C (528 / 217 : Real) * Polynomial.X).natDegree <= 2 := by
    apply le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    . simp
    . exact hlin.trans (by decide)
  exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hleft hquad)

/-- A power-k filter requires at most degree 2k. -/
theorem natDegree_reciprocalWindowQuadratic_pow_le (k : Nat) :
    (reciprocalWindowQuadratic ^ k).natDegree <= 2 * k := by
  rw [Polynomial.natDegree_pow]
  simpa only [Nat.mul_comm k 2] using
    Nat.mul_le_mul_left k natDegree_reciprocalWindowQuadratic_le

/-- Uniform norm on exactly the retained entering/leaving coordinate window. -/
theorem abs_eval_reciprocalWindowQuadratic_le (x : Real)
    (hlo : (1 / 2 : Real) <= x) (hup : x <= 4 / 3) :
    abs (Polynomial.eval x reciprocalWindowQuadratic) <= 25 / 217 := by
  have hleft : 0 <= 5 - (12 * x - 11) := by linarith only [hup]
  have hright : 0 <= 5 + (12 * x - 11) := by linarith only [hlo]
  have hsq : (12 * x - 11) ^ 2 <= 25 := by
    nlinarith only [mul_nonneg hleft hright]
  rw [eval_reciprocalWindowQuadratic]
  apply abs_le.mpr
  constructor <;> nlinarith only [hsq, sq_nonneg (12 * x - 11)]

/-- Every power gives a certified uniform filter norm. -/
theorem abs_eval_reciprocalWindowQuadratic_pow_le (k : Nat) (x : Real)
    (hlo : (1 / 2 : Real) <= x) (hup : x <= 4 / 3) :
    abs (Polynomial.eval x (reciprocalWindowQuadratic ^ k)) <=
      (25 / 217 : Real) ^ k := by
  rw [Polynomial.eval_pow, abs_pow]
  have hb := abs_eval_reciprocalWindowQuadratic_le x hlo hup
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hb (abs_nonneg _) (by positivity)

/-- A convenient rational geometric rate for the complete squared error. -/
theorem reciprocalWindowQuadratic_rate (k : Nat) :
    ((25 / 217 : Real) ^ k) ^ 2 <= (1 / 64 : Real) ^ k := by
  have hb : (25 / 217 : Real) ^ 2 <= (1 / 64 : Real) := by norm_num
  rw [<- pow_mul, Nat.mul_comm k 2, pow_mul]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hb (sq_nonneg _)
        (pow_nonneg (by norm_num : (0 : Real) <= 1 / 64) k)

end Polynomial
