/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.ReciprocalChebyshevCore

/-!
# A rational characteristic filter for the integrated reciprocal window

The complete normalizer has the exact rational branches seven and one seventh.
The filter is normalized at zero and bounded only on the retained cost window.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Polynomial

/-- Both characteristic powers are retained, including the order-zero case. -/
def reciprocalSevenDenominator (k : Nat) : Real :=
  (7 : Real) ^ k + (1 / 7 : Real) ^ k

/-- The normalizer is the exterior rotation value at the rational reference. -/
theorem reciprocalSeven_exact_normalizer (k : Nat) :
    reciprocalSevenDenominator k =
      2 * Polynomial.eval (25 / 7 : Real) (reciprocalChebyshevT k) := by
  have h := reciprocalChebyshev_characteristic_identity k (25 / 7 : Real)
    (24 / 7 : Real) (by norm_num)
  norm_num at h
  dsimp only [reciprocalSevenDenominator]
  linarith only [h.1, h.2]

/-- The denominator is strictly positive before any normalization. -/
theorem reciprocalSevenDenominator_pos (k : Nat) : 0 < reciprocalSevenDenominator k := by
  dsimp only [reciprocalSevenDenominator]
  positivity

/-- The rational characteristic window filter. -/
def reciprocalSevenFilter (k : Nat) : Polynomial Real :=
  Polynomial.C (2 / reciprocalSevenDenominator k) *
    (reciprocalChebyshevT k).comp
      (Polynomial.C (25 / 7 : Real) - Polynomial.C (128 / 35 : Real) * Polynomial.X)

/-- The exact affine argument with its full signed normalizer. -/
theorem eval_reciprocalSevenFilter (k : Nat) (x : Real) :
    Polynomial.eval x (reciprocalSevenFilter k) =
      2 * Polynomial.eval ((125 - 128 * x) / 35) (reciprocalChebyshevT k) /
        reciprocalSevenDenominator k := by
  simp only [reciprocalSevenFilter, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X]
  have harg : (25 / 7 : Real) - (128 / 35 : Real) * x = (125 - 128 * x) / 35 := by ring
  rw [harg]
  ring

/-- The moment representation is normalized at zero at every order. -/
theorem eval_zero_reciprocalSevenFilter (k : Nat) :
    Polynomial.eval 0 (reciprocalSevenFilter k) = 1 := by
  rw [eval_reciprocalSevenFilter]
  have harg : ((125 : Real) - 128 * 0) / 35 = 25 / 7 := by norm_num
  rw [harg, <- reciprocalSeven_exact_normalizer]
  exact div_self (reciprocalSevenDenominator_pos k).ne'

/-- The affine filter retains degree at most the chosen order. -/
theorem natDegree_reciprocalSevenFilter_le (k : Nat) :
    (reciprocalSevenFilter k).natDegree <= k := by
  let q : Polynomial Real :=
    Polynomial.C (25 / 7 : Real) - Polynomial.C (128 / 35 : Real) * Polynomial.X
  have hlin : q.natDegree <= 1 := by
    apply le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    . simp
    . calc
        _ <= (Polynomial.C (128 / 35 : Real)).natDegree +
            (Polynomial.X : Polynomial Real).natDegree := Polynomial.natDegree_mul_le
        _ = 1 := by simp
  have hcomp : ((reciprocalChebyshevT k).comp q).natDegree <= k := by
    calc
      _ <= (reciprocalChebyshevT k).natDegree * q.natDegree := Polynomial.natDegree_comp_le
      _ <= k * 1 := Nat.mul_le_mul (reciprocalChebyshev_degrees k).1 hlin
      _ = k := by omega
  calc
    _ <= (Polynomial.C (2 / reciprocalSevenDenominator k)).natDegree +
        ((reciprocalChebyshevT k).comp q).natDegree := Polynomial.natDegree_mul_le
    _ <= 0 + k := by simpa only [Polynomial.natDegree_C, zero_add] using hcomp
    _ = k := by omega

/-- The exact all-order norm on the integrated cost window. -/
theorem abs_eval_reciprocalSevenFilter_le_exact (k : Nat) (x : Real)
    (hlo : (45 / 64 : Real) <= x) (hup : x <= 5 / 4) :
    abs (Polynomial.eval x (reciprocalSevenFilter k)) <=
      2 / reciprocalSevenDenominator k := by
  have hn := abs_eval_reciprocalChebyshevT_le_one k ((125 - 128 * x) / 35)
    (by linarith only [hup]) (by linarith only [hlo])
  rw [eval_reciprocalSevenFilter, abs_div, abs_mul,
    abs_of_pos (by norm_num : (0 : Real) < 2), abs_of_pos (reciprocalSevenDenominator_pos k)]
  exact div_le_div_of_nonneg_right
    (by nlinarith only [hn] : 2 * abs (Polynomial.eval ((125 - 128 * x) / 35)
      (reciprocalChebyshevT k)) <= 2) (reciprocalSevenDenominator_pos k).le

/-- The exact denominator yields a simple geometric norm at the same degree. -/
theorem reciprocalSeven_filter_norm_rate (k : Nat) :
    2 / reciprocalSevenDenominator k <= 2 * (1 / 7 : Real) ^ k := by
  have hd := reciprocalSevenDenominator_pos k
  have hpow : (1 / 7 : Real) ^ k * (7 : Real) ^ k = 1 := by
    rw [<- mul_pow]
    norm_num
  have hmajor : (7 : Real) ^ k <= reciprocalSevenDenominator k := by
    dsimp only [reciprocalSevenDenominator]
    have h := pow_nonneg (by norm_num : (0 : Real) <= 1 / 7) k
    linarith only [h]
  have hm := mul_le_mul_of_nonneg_left hmajor
    (pow_nonneg (by norm_num : (0 : Real) <= 1 / 7) k)
  rw [hpow] at hm
  by_contra hn
  have hb := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hd
  have hid : 2 / reciprocalSevenDenominator k * reciprocalSevenDenominator k = 2 := by
    field_simp [hd.ne']
  rw [hid] at hb
  nlinarith only [hm, hb]

/-- Squaring the norm preserves the full base-forty-nine rate. -/
theorem reciprocalSevenFilter_rate (k : Nat) :
    (2 * (1 / 7 : Real) ^ k) ^ 2 = 4 * (1 / 49 : Real) ^ k := by
  rw [mul_pow, <- pow_mul, Nat.mul_comm k 2, pow_mul]
  norm_num

/-- The exact square rate retains the contracting characteristic branch. -/
theorem reciprocalSevenFilter_exact_rate (k : Nat) :
    (2 / reciprocalSevenDenominator k) ^ 2 =
      4 / (reciprocalSevenDenominator k) ^ 2 := by
  rw [div_pow]
  norm_num

end Polynomial
