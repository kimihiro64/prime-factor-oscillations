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
# Joint positivity of compensated reflected resolvents

The two horizontal reflections and the two evaluation lines remain coupled.
The exact numerator is positive throughout the strip r^2 >= 2*x^2.
The infinitesimal numerator has this threshold if and only if it is
nonnegative at every vertical displacement.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

def pairedResolventDen (r x y : Real) : Real :=
  ((r - x) ^ 2 + y ^ 2) * ((r + x) ^ 2 + y ^ 2)

def pairedResolventMean (r x y : Real) : Real :=
  ((r - x) / ((r - x) ^ 2 + y ^ 2) +
    (r + x) / ((r + x) ^ 2 + y ^ 2)) / 2

def pairedResolventGram (r R x y : Real) : Real :=
  (r ^ 2 + y ^ 2 - x ^ 2) * (R ^ 2 + y ^ 2 - x ^ 2) -
    4 * y ^ 2 * x ^ 2

def pairedResolventDifference (r R x y : Real) : Real :=
  pairedResolventMean r x y - r / R * pairedResolventMean R x y

theorem pairedResolventDen_pos (r x y : Real) (hr : abs x < r) :
    0 < pairedResolventDen r x y := by
  have hx := abs_lt.mp hr
  have hm : 0 < r - x := by linarith only [hx.2]
  have hp : 0 < r + x := by linarith only [hx.1]
  unfold pairedResolventDen
  exact mul_pos
    (by nlinarith only [sq_pos_of_pos hm, sq_nonneg y])
    (by nlinarith only [sq_pos_of_pos hp, sq_nonneg y])

theorem pairedResolventMean_formula (r x y : Real) (hr : abs x < r) :
    pairedResolventMean r x y =
      r * (r ^ 2 + y ^ 2 - x ^ 2) / pairedResolventDen r x y := by
  have hx := abs_lt.mp hr
  have hm : Not ((r - x) ^ 2 + y ^ 2 = 0) := by
    have hh : 0 < r - x := by linarith only [hx.2]
    exact ne_of_gt (by nlinarith only [sq_pos_of_pos hh, sq_nonneg y])
  have hp : Not ((r + x) ^ 2 + y ^ 2 = 0) := by
    have hh : 0 < r + x := by linarith only [hx.1]
    exact ne_of_gt (by nlinarith only [sq_pos_of_pos hh, sq_nonneg y])
  unfold pairedResolventMean pairedResolventDen
  field_simp [hm, hp]
  ring

theorem pairedResolventGram_nonneg (r R x y : Real)
    (hr : 2 * x ^ 2 <= r ^ 2) (hR : r ^ 2 <= R ^ 2) :
    0 <= pairedResolventGram r R x y := by
  have hk : 0 <= r ^ 2 - 2 * x ^ 2 := by linarith only [hr]
  have hMinus := add_nonneg (sq_nonneg (y - x)) hk
  have hPlus := add_nonneg (sq_nonneg (y + x)) hk
  have hProduct := mul_nonneg hMinus hPlus
  have hA : 0 <= r ^ 2 + y ^ 2 - x ^ 2 := by
    nlinarith only [hr, sq_nonneg x, sq_nonneg y]
  have hExtra := mul_nonneg (sub_nonneg.mpr hR) hA
  unfold pairedResolventGram
  nlinarith only [hProduct, hExtra]

theorem pairedResolventGram_sharp (r x : Real) :
    (forall y : Real, 0 <= pairedResolventGram r r x y) <->
      2 * x ^ 2 <= r ^ 2 := by
  constructor
  . intro h
    have hp := h x
    unfold pairedResolventGram at hp
    by_contra hn
    have hlt : 0 < 2 * x ^ 2 - r ^ 2 := by linarith only [lt_of_not_ge hn]
    have hsum : 0 < 2 * x ^ 2 + r ^ 2 := by
      nlinarith only [hlt, sq_nonneg r]
    have hmul := mul_pos hlt hsum
    nlinarith only [hp, hmul]
  . intro hr y
    exact pairedResolventGram_nonneg r r x y hr le_rfl

theorem pairedResolventDifference_formula (r R x y : Real)
    (hr : abs x < r) (hR : r < R) :
    pairedResolventDifference r R x y =
      r * (R ^ 2 - r ^ 2) * pairedResolventGram r R x y /
        (pairedResolventDen r x y * pairedResolventDen R x y) := by
  have hRR : abs x < R := hr.trans hR
  have hr0 : 0 < r := (abs_nonneg x).trans_lt hr
  have hR0 : Not (R = 0) := ne_of_gt (hr0.trans hR)
  have hd0 := ne_of_gt (pairedResolventDen_pos r x y hr)
  have hd1 := ne_of_gt (pairedResolventDen_pos R x y hRR)
  unfold pairedResolventDifference
  rw [pairedResolventMean_formula r x y hr,
    pairedResolventMean_formula R x y hRR]
  unfold pairedResolventGram
  field_simp [hR0, hd0, hd1]
  unfold pairedResolventDen
  ring

theorem pairedResolventDifference_nonneg (r R x y : Real)
    (hr : abs x < r) (hR : r < R) (hStrip : 2 * x ^ 2 <= r ^ 2) :
    0 <= pairedResolventDifference r R x y := by
  have hr0 : 0 < r := (abs_nonneg x).trans_lt hr
  have hRR : abs x < R := hr.trans hR
  have hsq : r ^ 2 <= R ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hR.le)
      (show 0 <= R + r by linarith)
    nlinarith only [h]
  rw [pairedResolventDifference_formula r R x y hr hR]
  exact div_nonneg
    (mul_nonneg (mul_nonneg hr0.le (sub_nonneg.mpr hsq))
      (pairedResolventGram_nonneg r R x y hStrip hsq))
    (mul_nonneg (pairedResolventDen_pos r x y hr).le
      (pairedResolventDen_pos R x y hRR).le)

theorem pairedResolventDifference_center (r R : Real) (hr : 0 < r)
    (hR : r < R) :
    pairedResolventDifference r R 0 0 = 1 / r - r / R ^ 2 := by
  have hR0 : Not (R = 0) := ne_of_gt (hr.trans hR)
  unfold pairedResolventDifference pairedResolventMean
  field_simp [hr.ne', hR0]
  ring

theorem pairedResolventDifference_center_pos (r R : Real)
    (hr : 0 < r) (hR : r < R) :
    0 < pairedResolventDifference r R 0 0 := by
  rw [pairedResolventDifference_center r R hr hR]
  have hR0 : 0 < R := hr.trans hR
  have hGain : (1 / r - r / R ^ 2) * (r * R ^ 2) = R ^ 2 - r ^ 2 := by
    field_simp [hr.ne', hR0.ne']
  have hsq : 0 < R ^ 2 - r ^ 2 := by
    have h := mul_pos (sub_pos.mpr hR) (show 0 < R + r by linarith)
    nlinarith only [h]
  by_contra hn
  have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
    (mul_nonneg hr.le (sq_nonneg R))
  nlinarith only [hh, hGain, hsq]

theorem pairedResolventDifference_same_height_min (r R x : Real)
    (hr : abs x < r) (hR : r < R) :
    pairedResolventDifference r R 0 0 <= pairedResolventDifference r R x 0 := by
  have hx := abs_lt.mp hr
  have hr0 : 0 < r := (abs_nonneg x).trans_lt hr
  have hR0 : 0 < R := hr0.trans hR
  have hm : 0 < r - x := by linarith only [hx.2]
  have hp : 0 < r + x := by linarith only [hx.1]
  have hRm : 0 < R - x := by linarith only [hx.2, hR]
  have hRp : 0 < R + x := by linarith only [hx.1, hR]
  have hA : 0 < r ^ 2 - x ^ 2 := by
    nlinarith only [mul_pos hm hp]
  have hB : 0 < R ^ 2 - x ^ 2 := by
    nlinarith only [mul_pos hRm hRp]
  have hN : 0 <= r * (R ^ 2 - r ^ 2) := by
    have h := mul_pos (sub_pos.mpr hR) (show 0 < R + r by linarith)
    apply mul_nonneg hr0.le
    nlinarith only [h]
  have hD : (r ^ 2 - x ^ 2) * (R ^ 2 - x ^ 2) <= r ^ 2 * R ^ 2 := by
    exact mul_le_mul (by nlinarith only [sq_nonneg x])
      (by nlinarith only [sq_nonneg x]) hB.le (sq_nonneg r)
  have hVal : pairedResolventDifference r R x 0 =
      r * (R ^ 2 - r ^ 2) / ((r ^ 2 - x ^ 2) * (R ^ 2 - x ^ 2)) := by
    unfold pairedResolventDifference pairedResolventMean
    field_simp [hm.ne', hp.ne', hRm.ne', hRp.ne', hR0.ne', hA.ne', hB.ne']
    ring
  have hVal0 : pairedResolventDifference r R 0 0 =
      r * (R ^ 2 - r ^ 2) / (r ^ 2 * R ^ 2) := by
    rw [pairedResolventDifference_center r R hr0 hR]
    field_simp [hr0.ne', hR0.ne']
  rw [hVal0, hVal]
  exact div_le_div_of_nonneg_left hN (mul_pos hA hB) hD

end Complex
