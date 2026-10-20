/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.PolynomialReciprocalTransport

/-!
# Coupled polynomial rotation for reciprocal Chebyshev filters

The two polynomial coordinates preserve a quadratic form. On the unit
interval this bounds the first coordinate by one. At 11/5 a rational
invariant cone gives a positive normalizer growing at least as 4^k/2.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Polynomial

/-- Coupled first-kind and second-kind Chebyshev coordinates, initialized at (1,0). -/
def reciprocalChebyshevPair : Nat -> Prod (Polynomial Real) (Polynomial Real)
  | 0 => (1, 0)
  | k + 1 =>
      let v := reciprocalChebyshevPair k
      (Polynomial.X * v.1 - (1 - Polynomial.X ^ 2) * v.2,
        v.1 + Polynomial.X * v.2)

def reciprocalChebyshevT (k : Nat) : Polynomial Real := (reciprocalChebyshevPair k).1

def reciprocalChebyshevU (k : Nat) : Polynomial Real := (reciprocalChebyshevPair k).2

theorem reciprocalChebyshevT_zero : reciprocalChebyshevT 0 = 1 := rfl

theorem reciprocalChebyshevU_zero : reciprocalChebyshevU 0 = 0 := rfl

theorem reciprocalChebyshevT_succ (k : Nat) :
    reciprocalChebyshevT (k + 1) =
      Polynomial.X * reciprocalChebyshevT k -
        (1 - Polynomial.X ^ 2) * reciprocalChebyshevU k := rfl

theorem reciprocalChebyshevU_succ (k : Nat) :
    reciprocalChebyshevU (k + 1) =
      reciprocalChebyshevT k + Polynomial.X * reciprocalChebyshevU k := rfl

/-- The coupled degrees retain the one-degree offset, including the zero start. -/
theorem reciprocalChebyshev_degrees (k : Nat) :
    (reciprocalChebyshevT k).natDegree <= k /\
      (reciprocalChebyshevU k).natDegree <= k - 1 := by
  induction k with
  | zero => simp [reciprocalChebyshevT_zero, reciprocalChebyshevU_zero]
  | succ k ih =>
      by_cases hk : k = 0
      case pos =>
        subst k
        simp [reciprocalChebyshevT_succ, reciprocalChebyshevU_succ,
          reciprocalChebyshevT_zero, reciprocalChebyshevU_zero]
      case neg =>
        have hk1 : 1 <= k := by omega
        have hd : (1 - (Polynomial.X : Polynomial Real) ^ 2).natDegree <= 2 := by
          apply le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
          . simp
          . simp
        have hxt : (Polynomial.X * reciprocalChebyshevT k).natDegree <= k + 1 := by
          calc
            _ <= (Polynomial.X : Polynomial Real).natDegree +
                (reciprocalChebyshevT k).natDegree := Polynomial.natDegree_mul_le
            _ <= 1 + k := by simpa using Nat.add_le_add_left ih.1 1
            _ = k + 1 := by omega
        have hdu : ((1 - Polynomial.X ^ 2) * reciprocalChebyshevU k).natDegree <= k + 1 := by
          calc
            _ <= (1 - (Polynomial.X : Polynomial Real) ^ 2).natDegree +
                (reciprocalChebyshevU k).natDegree := Polynomial.natDegree_mul_le
            _ <= 2 + (k - 1) := Nat.add_le_add hd ih.2
            _ <= k + 1 := by omega
        have hxu : (Polynomial.X * reciprocalChebyshevU k).natDegree <= k := by
          calc
            _ <= (Polynomial.X : Polynomial Real).natDegree +
                (reciprocalChebyshevU k).natDegree := Polynomial.natDegree_mul_le
            _ <= 1 + (k - 1) := by simpa using Nat.add_le_add_left ih.2 1
            _ <= k := by omega
        rw [reciprocalChebyshevT_succ, reciprocalChebyshevU_succ]
        constructor
        . exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le hxt hdu)
        . simpa only [Nat.add_sub_cancel] using
            le_trans (Polynomial.natDegree_add_le _ _) (max_le ih.1 hxu)

/-- The exact quadratic-form invariant, before any sign or norm estimate. -/
theorem reciprocalChebyshev_eval_identity (k : Nat) (x : Real) :
    (Polynomial.eval x (reciprocalChebyshevT k)) ^ 2 +
      (1 - x ^ 2) * (Polynomial.eval x (reciprocalChebyshevU k)) ^ 2 = 1 := by
  induction k with
  | zero => simp [reciprocalChebyshevT_zero, reciprocalChebyshevU_zero]
  | succ k ih =>
      rw [reciprocalChebyshevT_succ, reciprocalChebyshevU_succ]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_add]
      calc
        _ = (Polynomial.eval x (reciprocalChebyshevT k)) ^ 2 +
            (1 - x ^ 2) * (Polynomial.eval x (reciprocalChebyshevU k)) ^ 2 := by ring
        _ = 1 := ih

/-- The retained first coordinate has norm at most one on the complete unit interval. -/
theorem abs_eval_reciprocalChebyshevT_le_one (k : Nat) (x : Real)
    (hlo : -1 <= x) (hup : x <= 1) :
    abs (Polynomial.eval x (reciprocalChebyshevT k)) <= 1 := by
  have hd : 0 <= 1 - x ^ 2 := by
    have hm := mul_nonneg (by linarith only [hup] : 0 <= 1 - x)
      (by linarith only [hlo] : 0 <= 1 + x)
    nlinarith only [hm]
  have hid := reciprocalChebyshev_eval_identity k x
  have hn := mul_nonneg hd (sq_nonneg (Polynomial.eval x (reciprocalChebyshevU k)))
  have hsq : (Polynomial.eval x (reciprocalChebyshevT k)) ^ 2 <= 1 := by
    nlinarith only [hid, hn]
  apply abs_le.mpr
  constructor <;> nlinarith only [hsq]

/-- A rational invariant cone proves growth of the complete coupled normalizer. -/
theorem reciprocalChebyshev_positive_growth_packet (k : Nat) :
    0 <= Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevU k) /\
      (9 / 5 : Real) * Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevU k) <=
        Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) /\
      (4 : Real) ^ k <=
        Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) +
          (9 / 5 : Real) * Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevU k) := by
  induction k with
  | zero => norm_num [reciprocalChebyshevT_zero, reciprocalChebyshevU_zero]
  | succ k ih =>
      let A : Real := Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k)
      let B : Real := Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevU k)
      have hA : (9 / 5 : Real) * B <= A := ih.2.1
      have hB : 0 <= B := ih.1
      have hg : (4 : Real) ^ k <= A + (9 / 5 : Real) * B := ih.2.2
      have hT : Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT (k + 1)) =
          (11 / 5 : Real) * A + (96 / 25 : Real) * B := by
        rw [reciprocalChebyshevT_succ]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_one, Polynomial.eval_pow]
        dsimp only [A, B]
        ring
      have hU : Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevU (k + 1)) =
          A + (11 / 5 : Real) * B := by
        rw [reciprocalChebyshevU_succ]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        rfl
      rw [hT, hU, pow_succ]
      constructor
      . linarith only [hA, hB]
      . constructor
        . linarith only [hA, hB]
        . linarith only [hg, hB]

/-- The normalizing denominator is positive and at least half of 4^k. -/
theorem reciprocalChebyshev_normalizer_lower (k : Nat) :
    0 < Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) /\
      (4 : Real) ^ k <= 2 *
        Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) := by
  have hp := reciprocalChebyshev_positive_growth_packet k
  have hg : (4 : Real) ^ k <= 2 *
      Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) := by
    linarith only [hp.2.1, hp.2.2]
  exact And.intro (by linarith only [hg, pow_pos (by norm_num : (0 : Real) < 4) k]) hg

end Polynomial
