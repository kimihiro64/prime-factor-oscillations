/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Real.Sqrt
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

/-- The expanding characteristic root of the fixed retained-window normalization. -/
def reciprocalChebyshevLambda : Real := (11 + 4 * Real.sqrt 6) / 5

/-- The contracting characteristic root, retained in the exact normalizer. -/
def reciprocalChebyshevMu : Real := (11 - 4 * Real.sqrt 6) / 5

/-- Both characteristic branches of the complete normalization denominator. -/
def reciprocalChebyshevDenominator (k : Nat) : Real :=
  reciprocalChebyshevLambda ^ k + reciprocalChebyshevMu ^ k

/-- Retain both characteristic powers instead of a one-sided growth envelope. -/
theorem reciprocalChebyshev_exact_normalizer (k : Nat) :
    reciprocalChebyshevDenominator k =
      2 * Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : Real) <= 6)
  have hc : (4 * Real.sqrt 6 / 5) ^ 2 = (11 / 5 : Real) ^ 2 - 1 := by
    nlinarith only [hs]
  have hp := reciprocalChebyshev_characteristic_identity k (11 / 5 : Real)
    (4 * Real.sqrt 6 / 5) hc
  have hplus : (11 / 5 : Real) + 4 * Real.sqrt 6 / 5 = reciprocalChebyshevLambda := by
    dsimp only [reciprocalChebyshevLambda]
    ring
  have hminus : (11 / 5 : Real) - 4 * Real.sqrt 6 / 5 = reciprocalChebyshevMu := by
    dsimp only [reciprocalChebyshevMu]
    ring
  rw [hplus, hminus] at hp
  dsimp only [reciprocalChebyshevDenominator]
  linarith only [hp.1, hp.2]

/-- The exact roots are positive reciprocals and the expanding root exceeds four. -/
theorem reciprocalChebyshev_spectral_data :
    4 < reciprocalChebyshevLambda /\
      0 < reciprocalChebyshevMu /\
      reciprocalChebyshevLambda * reciprocalChebyshevMu = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : Real) <= 6)
  have hs0 := Real.sqrt_nonneg 6
  have hl : 4 < reciprocalChebyshevLambda := by
    dsimp only [reciprocalChebyshevLambda]
    nlinarith only [hs, hs0]
  have hprod : reciprocalChebyshevLambda * reciprocalChebyshevMu = 1 := by
    dsimp only [reciprocalChebyshevLambda, reciprocalChebyshevMu]
    nlinarith only [hs]
  have hm : 0 < reciprocalChebyshevMu := by
    by_contra hn
    have hb := mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (lt_trans (by norm_num : (0 : Real) < 4) hl)) (le_of_not_gt hn)
    rw [hprod] at hb
    linarith only [hb]
  exact And.intro hl (And.intro hm hprod)

/-- Every exact normalizing denominator is strictly positive before division. -/
theorem reciprocalChebyshevDenominator_pos (k : Nat) :
    0 < reciprocalChebyshevDenominator k := by
  rw [reciprocalChebyshev_exact_normalizer]
  exact mul_pos (by norm_num) (reciprocalChebyshev_normalizer_lower k).1

/-- The exact complete denominator gives the sharper retained-window norm. -/
theorem abs_eval_reciprocalChebyshevFilter_le_exact (k : Nat) (x : Real)
    (hlo : (1 / 2 : Real) <= x) (hup : x <= 4 / 3) :
    abs (Polynomial.eval x (reciprocalChebyshevFilter k)) <=
      2 / reciprocalChebyshevDenominator k := by
  have hn := abs_eval_reciprocalChebyshevT_le_one k ((11 - 12 * x) / 5)
    (by linarith only [hup]) (by linarith only [hlo])
  have hd := (reciprocalChebyshev_normalizer_lower k).1
  have hrecip : 1 / Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) =
      2 / reciprocalChebyshevDenominator k := by
    rw [reciprocalChebyshev_exact_normalizer]
    field_simp [hd.ne']
  calc
    _ = abs (Polynomial.eval ((11 - 12 * x) / 5) (reciprocalChebyshevT k)) /
        Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) := by
          rw [eval_reciprocalChebyshevFilter, abs_div, abs_of_pos hd]
    _ <= 1 / Polynomial.eval (11 / 5 : Real) (reciprocalChebyshevT k) := by
      have hm := mul_le_mul_of_nonneg_right hn
        (div_nonneg (by norm_num : (0 : Real) <= 1) hd.le)
      simpa only [div_eq_mul_inv, one_mul] using hm
    _ = 2 / reciprocalChebyshevDenominator k := hrecip

/-- The exact square-filter error conversion, without discarding either branch. -/
theorem reciprocalChebyshevFilter_exact_rate (k : Nat) :
    (2 / reciprocalChebyshevDenominator k) ^ 2 =
      4 / (reciprocalChebyshevDenominator k) ^ 2 := by
  rw [div_pow]
  norm_num

end Polynomial
