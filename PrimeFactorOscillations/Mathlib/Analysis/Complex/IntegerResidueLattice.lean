/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact spacing of an integer residue lattice

The affine residue map has a discrete two-dimensional range. At height at
least d * (d - 1), its minimum nonzero distance is exactly
d * (d - 1) / norm (z + d - 1). Both integer coordinates are unrestricted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

def integerResidueCode (d : Nat) (z : Complex) (a b : Int) : Complex :=
  -(a : Complex) + (d : Complex) * z / (z + (d : Complex) - 1) * (b : Complex)

theorem integerResidueCode_mul_den (d : Nat) (z : Complex) (a b : Int)
    (hden : Not (z + (d : Complex) - 1 = 0)) :
    integerResidueCode d z a b * (z + (d : Complex) - 1) =
      z * ((d : Complex) * (b : Complex) - (a : Complex)) -
        ((d : Complex) - 1) * (a : Complex) := by
  unfold integerResidueCode
  field_simp [hden]
  ring

theorem integerResidueCode_sub (d : Nat) (z : Complex) (a b a' b' : Int) :
    integerResidueCode d z a b - integerResidueCode d z a' b' =
      integerResidueCode d z (a - a') (b - b') := by
  unfold integerResidueCode
  push_cast
  ring

private theorem intCast_abs_one_le (a : Int) (ha : Not (a = 0)) :
    (1 : Real) <= abs (a : Real) := by
  rcases lt_or_gt_of_ne ha with hn | hp
  . have hi : a <= -1 := by omega
    have hr : (a : Real) <= -1 := by exact_mod_cast hi
    have h := neg_le_abs (a : Real)
    linarith
  . have hi : 1 <= a := by omega
    have hr : (1 : Real) <= (a : Real) := by exact_mod_cast hi
    exact hr.trans (le_abs_self _)

theorem integerResidueCode_integer_im (d : Nat) (z : Complex) (a b : Int)
    (hden : Not (z + (d : Complex) - 1 = 0)) :
    (integerResidueCode d z a b * (z + (d : Complex) - 1)).im =
      (((d : Int) * b - a : Int) : Real) * z.im := by
  rw [integerResidueCode_mul_den d z a b hden]
  simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, Complex.intCast_re, Complex.intCast_im,
    Complex.one_im]
  push_cast
  ring

/-- The nonzero integer imaginary coordinate already gives a full height. -/
theorem integerResidueCode_nonresonant_separation
    (d : Nat) (z : Complex) (a b : Int)
    (hden : Not (z + (d : Complex) - 1 = 0))
    (hk : Not ((d : Int) * b - a = 0)) :
    abs z.im <= norm (integerResidueCode d z a b) * norm (z + (d : Complex) - 1) := by
  have hi := intCast_abs_one_le ((d : Int) * b - a) hk
  have h := Complex.abs_im_le_norm
    (integerResidueCode d z a b * (z + (d : Complex) - 1))
  rw [integerResidueCode_integer_im d z a b hden, abs_mul, norm_mul] at h
  exact (by nlinarith [abs_nonneg z.im] :
    abs z.im <= abs (((d : Int) * b - a : Int) : Real) * abs z.im).trans h

/-- No nonzero lattice point lies below this bound at sufficiently large height. -/
theorem integerResidueCode_separation (d : Nat) (hd : 2 <= d)
    (z : Complex) (hz : (d : Real) * ((d : Real) - 1) <= abs z.im)
    (a b : Int) (hab : Not (a = 0 /\ b = 0))
    (hden : Not (z + (d : Complex) - 1 = 0)) :
    (d : Real) * ((d : Real) - 1) <=
      norm (integerResidueCode d z a b) * norm (z + (d : Complex) - 1) := by
  by_cases hk : (d : Int) * b - a = 0
  . have ha : a = (d : Int) * b := by omega
    have hb : Not (b = 0) := by
      intro hb
      apply hab
      exact And.intro (by rw [ha, hb]; simp) hb
    have hi := intCast_abs_one_le b hb
    have hdR : (2 : Real) <= d := by exact_mod_cast hd
    have hd0 : (0 : Real) <= d := by positivity
    have hd1 : 0 <= (d : Real) - 1 := by linarith
    have hRe :
        (integerResidueCode d z a b * (z + (d : Complex) - 1)).re =
          -((d : Real) * ((d : Real) - 1) * (b : Real)) := by
      rw [integerResidueCode_mul_den d z a b hden, ha]
      push_cast
      simp only [sub_self, mul_zero, zero_sub, Complex.neg_re,
        Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.natCast_re, Complex.natCast_im,
        Complex.intCast_re, Complex.intCast_im, Complex.one_re, Complex.one_im]
      ring
    have h := Complex.abs_re_le_norm
      (integerResidueCode d z a b * (z + (d : Complex) - 1))
    rw [hRe, abs_neg, abs_mul, abs_mul, abs_of_nonneg hd0,
      abs_of_nonneg hd1, norm_mul] at h
    have hp := mul_le_mul_of_nonneg_left hi (mul_nonneg hd0 hd1)
    have hp' : (d : Real) * ((d : Real) - 1) <=
        (d : Real) * ((d : Real) - 1) * abs (b : Real) := by
      simpa only [mul_one] using hp
    exact hp'.trans h
  . exact hz.trans (integerResidueCode_nonresonant_separation d z a b hden hk)

theorem integerResidueCode_pair_separation (d : Nat) (hd : 2 <= d)
    (z : Complex) (hz : (d : Real) * ((d : Real) - 1) <= abs z.im)
    (a b a' b' : Int) (hab : Not (a = a' /\ b = b'))
    (hden : Not (z + (d : Complex) - 1 = 0)) :
    (d : Real) * ((d : Real) - 1) <=
      norm (integerResidueCode d z a b - integerResidueCode d z a' b') *
        norm (z + (d : Complex) - 1) := by
  rw [integerResidueCode_sub]
  apply integerResidueCode_separation d hd z hz (a - a') (b - b') _ hden
  intro h
  apply hab
  exact And.intro (by omega) (by omega)

/-- The resonant pair (d,1) attains the separation bound exactly. -/
theorem integerResidueCode_attains (d : Nat) (hd : 2 <= d)
    (z : Complex) (hden : Not (z + (d : Complex) - 1 = 0)) :
    norm (integerResidueCode d z (d : Int) 1) * norm (z + (d : Complex) - 1) =
      (d : Real) * ((d : Real) - 1) := by
  rw [<- norm_mul, integerResidueCode_mul_den d z (d : Int) 1 hden]
  have he :
      z * ((d : Complex) * ((1 : Int) : Complex) - ((d : Int) : Complex)) -
        ((d : Complex) - 1) * ((d : Int) : Complex) =
      ((-((d : Real) * ((d : Real) - 1)) : Real) : Complex) := by
    push_cast
    ring
  rw [he]
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hd0 : (0 : Real) <= d := by positivity
  have hd1 : 0 <= (d : Real) - 1 := by linarith
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_neg, abs_mul, abs_of_nonneg hd0, abs_of_nonneg hd1]

end Complex

end
