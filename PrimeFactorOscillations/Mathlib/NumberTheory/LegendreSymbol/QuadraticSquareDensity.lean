/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticCharacterPolynomial

/-!
# Square-value counts and unit-density bounds

The affine and split nondegenerate quadratic formulas retain every
zero-value correction. For odd finite fields of cardinality at least
eleven, the square-value proportion on units is at most three quarters.
These classical local estimates supply finite independent prime tests.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace FiniteField

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Exact square-value count for any finite-field map, including zeros. -/
theorem twice_square_values_card (f : F -> F) :
    (2 : Int) * ((Finset.univ.filter (fun x : F => IsSquare (f x))).card : Int) =
      (Fintype.card F : Int) +
        (Finset.univ.sum fun x : F => (quadraticChar F) (f x)) +
        (Finset.univ.sum fun x : F => if f x = 0 then (1 : Int) else 0) := by
  have hPoint (x : F) :
      2 * (if IsSquare (f x) then (1 : Int) else 0) =
        1 + (quadraticChar F) (f x) + (if f x = 0 then 1 else 0) := by
    have h := twice_nonsquare_indicator (f x)
    by_cases hs : IsSquare (f x)
    . simp only [hs, ite_true] at h
      simp only [hs, ite_true]
      linarith only [h]
    . simp only [hs, ite_false] at h
      simp only [hs, ite_false]
      linarith only [h]
  have hCount :
      (Finset.univ.sum fun x : F => if IsSquare (f x) then (1 : Int) else 0) =
        ((Finset.univ.filter (fun x : F => IsSquare (f x))).card : Int) := by
    rw [<- Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  calc
    _ = Finset.univ.sum (fun x : F =>
        2 * (if IsSquare (f x) then (1 : Int) else 0)) := by
      rw [<- hCount, Finset.mul_sum]
    _ = _ := by
      simp_rw [hPoint]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]

/-- Every nonconstant affine map has exactly (q+1)/2 square values,
where zero is counted as a square. -/
theorem twice_affine_square_values_card (hF : Not (ringChar F = 2))
    (a b : F) (ha : Not (a = 0)) :
    (2 : Int) * ((Finset.univ.filter (fun x : F => IsSquare (a * x + b))).card : Int) =
      (Fintype.card F : Int) + 1 := by
  have h := twice_square_values_card (fun x : F => a * x + b)
  rw [quadraticChar_affine_sum hF a b ha, affine_zero_indicator_sum a b ha] at h
  simpa only [add_zero] using h

/-- The full split-quadratic count keeps both roots and the exact
leading-coefficient character. -/
theorem twice_split_quadratic_square_values_card (hF : Not (ringChar F = 2))
    (t a b : F) (ht : Not (t = 0)) (hab : Not (a = b)) :
    (2 : Int) *
        ((Finset.univ.filter (fun x : F => IsSquare (t * (x - a) * (x - b)))).card : Int) =
      (Fintype.card F : Int) + 2 - (quadraticChar F) t := by
  have hExpand (x : F) :
      t * (x - a) * (x - b) = t * x ^ 2 + (-t * (a + b)) * x + t * a * b := by
    ring
  have hDisc :
      (-t * (a + b)) ^ 2 - 4 * t * (t * a * b) = (t * (a - b)) ^ 2 := by ring
  have hFactor : Not (t * (a - b) = 0) := mul_ne_zero ht (sub_ne_zero.mpr hab)
  have hDiscNe : Not ((-t * (a + b)) ^ 2 - 4 * t * (t * a * b) = 0) := by
    rw [hDisc]
    exact pow_ne_zero 2 hFactor
  have hDiscChar :
      (quadraticChar F) ((-t * (a + b)) ^ 2 - 4 * t * (t * a * b)) = 1 := by
    rw [hDisc, map_pow, quadraticChar_sq_one hFactor]
  have hSum :
      (Finset.univ.sum fun x : F => (quadraticChar F) (t * (x - a) * (x - b))) =
        -(quadraticChar F) t := by
    simp_rw [hExpand]
    have h := quadraticChar_quadratic_sum hF t (-t * (a + b)) (t * a * b) ht
    rw [ite_eq_right hDiscNe] at h
    exact h
  have hZeros :
      (Finset.univ.sum fun x : F =>
        if t * (x - a) * (x - b) = 0 then (1 : Int) else 0) = 2 := by
    simp_rw [hExpand]
    have h := quadratic_zero_indicator_sum hF t (-t * (a + b)) (t * a * b) ht
    rw [hDiscChar] at h
    exact h.trans (by norm_num : (1 + 1 : Int) = 2)
  have h := twice_square_values_card (fun x : F => t * (x - a) * (x - b))
  rw [hSum, hZeros] at h
  linarith only [h]

/-- The affine square fraction on units is at most three quarters in
the stated positive-denominator range. -/
theorem four_affine_unit_square_card_le_three (hF : Not (ringChar F = 2))
    (hSize : 11 <= Fintype.card F) (a b : F) (ha : Not (a = 0)) :
    4 * (Finset.univ.filter (fun u : Units F => IsSquare (a * (u : F) + b))).card <=
      3 * (Fintype.card F - 1) := by
  have hSub :
      (Finset.univ.filter (fun u : Units F => IsSquare (a * (u : F) + b))).card <=
        (Finset.univ.filter (fun x : F => IsSquare (a * x + b))).card := by
    apply Finset.card_le_card_of_injOn (fun u : Units F => (u : F))
    . intro u hu
      exact Finset.mem_filter.mpr
        (And.intro (Finset.mem_univ _) (Finset.mem_filter.mp hu).2)
    . intro u hu v hv he
      exact Units.ext he
  have hSubInt :
      ((Finset.univ.filter (fun u : Units F => IsSquare (a * (u : F) + b))).card : Int) <=
        ((Finset.univ.filter (fun x : F => IsSquare (a * x + b))).card : Int) := by
    exact_mod_cast hSub
  have hCount := twice_affine_square_values_card hF a b ha
  have hn : (11 : Int) <= (Fintype.card F : Int) := by exact_mod_cast hSize
  have hOne : 1 <= Fintype.card F := (by decide : 1 <= 11).trans hSize
  have hDen : ((Fintype.card F - 1 : Nat) : Int) + 1 = (Fintype.card F : Int) := by
    exact_mod_cast Nat.sub_add_cancel hOne
  have hBound : (4 : Int) *
      ((Finset.univ.filter (fun u : Units F => IsSquare (a * (u : F) + b))).card : Int) <=
        3 * ((Fintype.card F - 1 : Nat) : Int) := by
    linarith only [hSubInt, hCount, hn, hDen]
  exact_mod_cast hBound

/-- The complete split-quadratic square fraction on units is uniformly
at most three quarters, with both exceptional roots retained. -/
theorem four_split_quadratic_unit_square_card_le_three
    (hF : Not (ringChar F = 2)) (hSize : 11 <= Fintype.card F)
    (t a b : F) (ht : Not (t = 0)) (hab : Not (a = b)) :
    4 * (Finset.univ.filter
      (fun u : Units F => IsSquare (t * ((u : F) - a) * ((u : F) - b)))).card <=
        3 * (Fintype.card F - 1) := by
  have hSub :
      (Finset.univ.filter
        (fun u : Units F => IsSquare (t * ((u : F) - a) * ((u : F) - b)))).card <=
      (Finset.univ.filter (fun x : F => IsSquare (t * (x - a) * (x - b)))).card := by
    apply Finset.card_le_card_of_injOn (fun u : Units F => (u : F))
    . intro u hu
      exact Finset.mem_filter.mpr
        (And.intro (Finset.mem_univ _) (Finset.mem_filter.mp hu).2)
    . intro u hu v hv he
      exact Units.ext he
  have hSubInt :
      ((Finset.univ.filter
        (fun u : Units F => IsSquare (t * ((u : F) - a) * ((u : F) - b)))).card : Int) <=
      ((Finset.univ.filter (fun x : F => IsSquare (t * (x - a) * (x - b)))).card : Int) := by
    exact_mod_cast hSub
  have hCount := twice_split_quadratic_square_values_card hF t a b ht hab
  have hChar : (quadraticChar F t) ^ 2 = 1 := quadraticChar_sq_one ht
  have hLower : (-1 : Int) <= quadraticChar F t := by
    nlinarith only [hChar, sq_nonneg (quadraticChar F t + 1)]
  have hn : (11 : Int) <= (Fintype.card F : Int) := by exact_mod_cast hSize
  have hOne : 1 <= Fintype.card F := (by decide : 1 <= 11).trans hSize
  have hDen : ((Fintype.card F - 1 : Nat) : Int) + 1 = (Fintype.card F : Int) := by
    exact_mod_cast Nat.sub_add_cancel hOne
  have hBound : (4 : Int) *
      ((Finset.univ.filter
        (fun u : Units F => IsSquare (t * ((u : F) - a) * ((u : F) - b)))).card : Int) <=
        3 * ((Fintype.card F - 1 : Nat) : Int) := by
    linarith only [hSubInt, hCount, hLower, hn, hDen]
  exact_mod_cast hBound

end FiniteField
