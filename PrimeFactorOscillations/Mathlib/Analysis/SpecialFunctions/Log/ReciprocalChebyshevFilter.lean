/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.ReciprocalChebyshevCore

/-!
# All-order normalized reciprocal Chebyshev filters

The denominator is proved positive before division. The shifted polynomial
is one at zero, has degree at most k, and has norm at most 2/4^k on the
complete retained reciprocal window [1/2,4/3].
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Polynomial

/-- Normalize the all-order rotation polynomial at the exterior reference point. -/
def reciprocalChebyshevFilter (k : Nat) : Polynomial Real :=
  Polynomial.C (1 / Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k)) *
    (reciprocalChebyshevT k).comp
      (Polynomial.C (11 / 5 : Real) - Polynomial.C (12 / 5 : Real) * Polynomial.X)

/-- The actual affine argument and complete normalizing denominator. -/
theorem eval_reciprocalChebyshevFilter (k : Nat) (x : Real) :
    Polynomial.eval x (reciprocalChebyshevFilter k) =
      Polynomial.eval ((11 - 12 * x) / 5) (reciprocalChebyshevT k) /
        Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) := by
  simp only [reciprocalChebyshevFilter, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X]
  have harg : (11 / 5 : Real) - (12 / 5 : Real) * x = (11 - 12 * x) / 5 := by ring
  rw [harg]
  ring

/-- The reference normalization is valid at every order, including zero. -/
theorem eval_zero_reciprocalChebyshevFilter (k : Nat) :
    Polynomial.eval 0 (reciprocalChebyshevFilter k) = 1 := by
  rw [eval_reciprocalChebyshevFilter]
  simp only [mul_zero, sub_zero]
  exact div_self (reciprocalChebyshev_normalizer_lower k).1.ne'

/-- An affine change of variable and scalar normalization preserve the degree bound. -/
theorem natDegree_reciprocalChebyshevFilter_le (k : Nat) :
    (reciprocalChebyshevFilter k).natDegree <= k := by
  let q : Polynomial Real :=
    Polynomial.C (11 / 5 : Real) - Polynomial.C (12 / 5 : Real) * Polynomial.X
  have hlin : q.natDegree <= 1 := by
    apply le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    . simp
    . calc
        _ <= (Polynomial.C (12 / 5 : Real)).natDegree +
            (Polynomial.X : Polynomial Real).natDegree := Polynomial.natDegree_mul_le
        _ = 1 := by simp
  have hcomp : ((reciprocalChebyshevT k).comp q).natDegree <= k := by
    calc
      _ <= (reciprocalChebyshevT k).natDegree * q.natDegree := Polynomial.natDegree_comp_le
      _ <= k * 1 := Nat.mul_le_mul (reciprocalChebyshev_degrees k).1 hlin
      _ = k := by omega
  calc
    _ <= (Polynomial.C (1 / Polynomial.eval (11 / 5 : Real)
          (reciprocalChebyshevT k))).natDegree +
        ((reciprocalChebyshevT k).comp q).natDegree := Polynomial.natDegree_mul_le
    _ <= 0 + k := by simpa only [Polynomial.natDegree_C, zero_add] using hcomp
    _ = k := by omega

/-- Uniform all-order suppression on the actual retained coordinate window. -/
theorem abs_eval_reciprocalChebyshevFilter_le (k : Nat) (x : Real)
    (hlo : (1 / 2 : Real) <= x) (hup : x <= 4 / 3) :
    abs (Polynomial.eval x (reciprocalChebyshevFilter k)) <=
      2 * (1 / 4 : Real) ^ k := by
  have hn := abs_eval_reciprocalChebyshevT_le_one k ((11 - 12 * x) / 5)
    (by linarith only [hup]) (by linarith only [hlo])
  have hd := reciprocalChebyshev_normalizer_lower k
  have hpower : (1 / 4 : Real) ^ k * (4 : Real) ^ k = 1 := by
    rw [<- mul_pow]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hd.2
    (pow_nonneg (by norm_num : (0 : Real) <= 1 / 4) k)
  rw [hpower] at hm
  rw [eval_reciprocalChebyshevFilter, abs_div, abs_of_pos hd.1]
  by_contra hb
  have hbad := mul_lt_mul_of_pos_right (lt_of_not_ge hb) hd.1
  have hcancel :
      abs (Polynomial.eval ((11 - 12 * x) / 5) (reciprocalChebyshevT k)) /
          Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) *
        Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) =
      abs (Polynomial.eval ((11 - 12 * x) / 5) (reciprocalChebyshevT k)) := by
    field_simp [hd.1.ne']
  rw [hcancel] at hbad
  nlinarith only [hbad, hm, hn]

/-- The complete squared filter rate used by the signed profile consumer. -/
theorem reciprocalChebyshevFilter_rate (k : Nat) :
    (2 * (1 / 4 : Real) ^ k) ^ 2 = 4 * (1 / 16 : Real) ^ k := by
  rw [mul_pow, <- pow_mul, Nat.mul_comm k 2, pow_mul]
  norm_num

end Polynomial
