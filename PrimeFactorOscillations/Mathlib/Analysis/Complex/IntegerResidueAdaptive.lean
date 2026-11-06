/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.Order.Floor.Ring
import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueUnitLattice

/-!
# Adaptive compensation attains the globally optimal noise threshold

In the closed critical strip at height H >= 2, every integer power d >= 2H
has exact unit lattice spacing. The explicit degree below therefore decodes
both unrestricted integer coordinates at every absolute error below one half.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

def adaptiveResidueDegree (z : Complex) : Nat :=
  max 4 (Nat.ceil (2 * abs z.im))

theorem adaptiveResidueDegree_ge_four (z : Complex) :
    4 <= adaptiveResidueDegree z :=
  Nat.le_max_left _ _

theorem adaptiveResidueDegree_ge_height (z : Complex) :
    2 * abs z.im <= (adaptiveResidueDegree z : Real) := by
  apply (Nat.le_ceil (2 * abs z.im)).trans
  exact_mod_cast Nat.le_max_right 4 (Nat.ceil (2 * abs z.im))

theorem integerResidueReference_im (d : Nat) (z : Complex) :
    ((d : Complex) * z / (z + (d : Complex) - 1)).im =
      (d : Real) * ((d : Real) - 1) * z.im /
        ((z.re + (d : Real) - 1) ^ 2 + z.im ^ 2) := by
  simp [Complex.div_im, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem integerResidueReference_unit (d : Nat) (z : Complex)
    (hRe : 0 <= z.re /\ z.re <= 1)
    (hHeight : 2 <= abs z.im)
    (hd : 2 * abs z.im <= (d : Real)) :
    1 <= abs (((d : Complex) * z / (z + (d : Complex) - 1)).im) := by
  let H := abs z.im
  let x := z.re + (d : Real) - 1
  have hH : (2 : Real) <= H := hHeight
  have hH0 : 0 <= H := abs_nonneg _
  have hHs : H ^ 2 = z.im ^ 2 := by
    exact sq_abs _
  have hd4 : (4 : Real) <= d := by linarith
  have hd0 : (0 : Real) <= d := by positivity
  have hd1 : 0 <= (d : Real) - 1 := by linarith
  have hx0 : 0 <= x := by dsimp [x]; linarith [hRe.1]
  have hx1 : x <= d := by dsimp [x]; linarith [hRe.2]
  have hxs : x ^ 2 <= (d : Real) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (add_nonneg hd0 hx0)]
  have hHsBound : H ^ 2 <= (d : Real) ^ 2 / 4 := by
    have hp := mul_nonneg (by linarith : 0 <= (d : Real) - 2 * H)
      (by positivity : 0 <= (d : Real) + 2 * H)
    nlinarith
  have hDen : 0 < x ^ 2 + z.im ^ 2 := by
    nlinarith [sq_nonneg x]
  have hDenBound : x ^ 2 + z.im ^ 2 <= 5 / 4 * (d : Real) ^ 2 := by
    nlinarith
  have hP0 : 0 <= (d : Real) * ((d : Real) - 1) :=
    mul_nonneg hd0 hd1
  have hNumLow := mul_le_mul_of_nonneg_right hH hP0
  have hdProduct : 0 <= (d : Real) * ((d : Real) - 4) :=
    mul_nonneg hd0 (by linarith)
  have hNum : x ^ 2 + z.im ^ 2 <=
      (d : Real) * ((d : Real) - 1) * H := by
    nlinarith [sq_nonneg (d : Real)]
  rw [integerResidueReference_im, abs_div, abs_mul, abs_mul,
    abs_of_nonneg hd0, abs_of_nonneg hd1, abs_of_pos hDen]
  have h := div_le_div_of_nonneg_right hNum hDen.le
  rw [div_self hDen.ne'] at h
  exact h

theorem integerResidueCode_large_power_spacing (d : Nat) (z : Complex)
    (hRe : 0 <= z.re /\ z.re <= 1)
    (hHeight : 2 <= abs z.im)
    (hd : 2 * abs z.im <= (d : Real)) :
    (forall a b a' b' : Int, Not (a = a' /\ b = b') ->
      1 <= norm (integerResidueCode d z a b - integerResidueCode d z a' b')) /\
      norm (integerResidueCode d z 1 0) = 1 := by
  have hv := integerResidueReference_unit d z hRe hHeight hd
  exact And.intro
    (fun a b a' b' hab => integerResidueCode_unit_pair_separation d z hv a b a' b' hab)
    (integerResidueCode_unit_attains d z)

theorem integerResidueCode_adaptive_spacing (z : Complex)
    (hRe : 0 <= z.re /\ z.re <= 1)
    (hHeight : 2 <= abs z.im) :
    (forall a b a' b' : Int, Not (a = a' /\ b = b') ->
      1 <= norm (integerResidueCode (adaptiveResidueDegree z) z a b -
        integerResidueCode (adaptiveResidueDegree z) z a' b')) /\
      norm (integerResidueCode (adaptiveResidueDegree z) z 1 0) = 1 :=
  integerResidueCode_large_power_spacing _ z hRe hHeight (adaptiveResidueDegree_ge_height z)

theorem integerResidueCode_large_power_unique (d : Nat) (z : Complex)
    (hRe : 0 <= z.re /\ z.re <= 1)
    (hHeight : 2 <= abs z.im)
    (hd : 2 * abs z.im <= (d : Real))
    (a b a' b' : Int) (r : Complex)
    (ha : norm (integerResidueCode d z a b - r) < 1 / 2)
    (hb : norm (integerResidueCode d z a' b' - r) < 1 / 2) :
    a = a' /\ b = b' :=
  integerResidueCode_unit_unique d z (integerResidueReference_unit d z hRe hHeight hd)
    a b a' b' r ha hb

theorem integerResidueCode_adaptive_unique (z : Complex)
    (hRe : 0 <= z.re /\ z.re <= 1)
    (hHeight : 2 <= abs z.im)
    (a b a' b' : Int) (r : Complex)
    (ha : norm (integerResidueCode (adaptiveResidueDegree z) z a b - r) < 1 / 2)
    (hb : norm (integerResidueCode (adaptiveResidueDegree z) z a' b' - r) < 1 / 2) :
    a = a' /\ b = b' :=
  integerResidueCode_large_power_unique _ z hRe hHeight (adaptiveResidueDegree_ge_height z)
    a b a' b' r ha hb

end Complex

end
