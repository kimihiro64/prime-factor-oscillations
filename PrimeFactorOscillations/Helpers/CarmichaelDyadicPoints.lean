/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Complex.Basic
import PrimeFactorOscillations.Helpers.CarmichaelDyadicWeights

/-!
# Injective reflected dyadic points and exact power references

Each word has a left and a right point, at the same positive height. The
complete infinite coding is injective before any finite-depth truncation.
The right-child collision between the quadratic and quartic maps is retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

def wordPoint (H : Real) (b : Bool) (w : List Bool) : Complex :=
  Complex.mk (if b then 1 - wordReal w else wordReal w) (wordHeight H w)

theorem wordPoint_im (H : Real) (b : Bool) (w : List Bool) :
    (wordPoint H b w).im = wordHeight H w := rfl

theorem wordPoint_bounds (H : Real) (b : Bool) (w : List Bool) :
    (1 / 7 : Real) <= (wordPoint H b w).re /\
      (wordPoint H b w).re <= (6 / 7 : Real) := by
  have h := wordReal_bounds w
  cases b
  . change (1 / 7 : Real) <= wordReal w /\ wordReal w <= 6 / 7
    constructor <;> linarith [h.1, h.2]
  . change (1 / 7 : Real) <= 1 - wordReal w /\ 1 - wordReal w <= 6 / 7
    constructor <;> linarith [h.1, h.2]

theorem wordPoint_injective (H : Real) :
    Function.Injective (fun p : Prod Bool (List Bool) => wordPoint H p.1 p.2) := by
  intro p q heq
  cases p with
  | mk b u =>
    cases q with
    | mk c v =>
      have hr := congrArg Complex.re heq
      have hu := wordReal_bounds u
      have hv := wordReal_bounds v
      cases b <;> cases c
      . have h : wordReal u = wordReal v := by simpa [wordPoint] using hr
        exact congrArg (Prod.mk false) (wordReal_injective h)
      . exfalso
        simp [wordPoint] at hr
        linarith [hu.2, hv.2]
      . exfalso
        simp [wordPoint] at hr
        linarith [hu.2, hv.2]
      . have h : wordReal u = wordReal v := by
          simp [wordPoint] at hr
          linarith
        exact congrArg (Prod.mk true) (wordReal_injective h)

theorem wordPoint_reflection (H : Real) (b : Bool) (w : List Bool) :
    wordPoint H (Bool.not b) w = 1 - star (wordPoint H b w) := by
  cases b <;> apply Complex.ext <;> simp [wordPoint]

theorem wordPoint_left_two (H : Real) (w : List Bool) :
    (wordPoint H false w + 1) / 2 = wordPoint H true (false :: w) := by
  apply Complex.ext
  . norm_num [wordPoint, wordReal, Complex.div_re, Complex.div_im]
    ring
  . norm_num [wordPoint, wordHeight_false, Complex.div_re, Complex.div_im]

theorem wordPoint_left_four (H : Real) (w : List Bool) :
    (wordPoint H false w + 3) / 4 = wordPoint H true (true :: w) := by
  apply Complex.ext
  . norm_num [wordPoint, wordReal, Complex.div_re, Complex.div_im]
    ring
  . norm_num [wordPoint, wordHeight_true, Complex.div_re, Complex.div_im]

theorem wordPoint_right_false_two (H : Real) (w : List Bool) :
    (wordPoint H true (false :: w) + 1) / 2 =
      wordPoint H true (true :: w) := by
  rw [<- wordPoint_left_two]
  calc
    ((wordPoint H false w + 1) / 2 + 1) / 2 =
        (wordPoint H false w + 3) / 4 := by ring
    _ = wordPoint H true (true :: w) := wordPoint_left_four H w

end PrimeFactorOscillations.CarmichaelDyadicSharpness
