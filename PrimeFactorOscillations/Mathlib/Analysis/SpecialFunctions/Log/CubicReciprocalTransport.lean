/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cubic compensation of reciprocal transport

The first two reciprocal powers preserve unit displacement and cancel its
quadratic error. The exact signed remainder has cubic displacement and
is nonnegative on either side of a common positive reference.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

/-- The unique two-power reciprocal weight with unit first-order response
and zero second-order response at the reference. -/
def cubicReciprocalTransport (r p : Real) : Real :=
  -3 * r ^ 2 / p + r ^ 3 / p ^ 2

/-- Exact cancellation, before taking any estimate of the remainder. -/
theorem cubicReciprocalTransport_sub (r p : Real)
    (hr : Not (r = 0)) (hp : Not (p = 0)) :
    cubicReciprocalTransport r p - cubicReciprocalTransport r r =
      (p - r) - (p - r) ^ 3 / p ^ 2 := by
  unfold cubicReciprocalTransport
  field_simp [hr, hp]
  ring

/-- A relative displacement bound gives an explicit cubic remainder. -/
theorem cubic_reciprocal_remainder_le (r C p x : Real)
    (hr : 0 < r) (hC : 0 <= C) (hp : 0 < p) (hx : 0 <= x)
    (hrelative : r * x <= 4 * C * p) :
    0 <= x ^ 3 / p ^ 2 /\
      x ^ 3 / p ^ 2 <= 16 * C ^ 2 * x / r ^ 2 := by
  have hprod := mul_nonneg (sub_nonneg.mpr hrelative)
    (by positivity : 0 <= 4 * C * p + r * x)
  have hsquare : (r * x) ^ 2 <= (4 * C * p) ^ 2 := by
    nlinarith only [hprod]
  have hmul := mul_le_mul_of_nonneg_right hsquare hx
  refine And.intro (by positivity) ?_
  have hid : (16 * C ^ 2 * x / r ^ 2 - x ^ 3 / p ^ 2) *
      (r ^ 2 * p ^ 2) = 16 * C ^ 2 * x * p ^ 2 - x ^ 3 * r ^ 2 := by
    field_simp [hr.ne', hp.ne']
  by_contra hn
  have hbad := mul_neg_of_neg_of_pos (sub_neg.mpr (lt_of_not_ge hn))
    (by positivity : 0 < r ^ 2 * p ^ 2)
  rw [hid] at hbad
  nlinarith only [hmul, hbad]

/-- The entering response retains its sign and a cubic-error lower bound. -/
theorem cubicReciprocalTransport_entering_bounds (r p C : Real)
    (hr : 0 < r) (hC : 0 <= C) (hrp : r <= p) (hgap : p - r <= 4 * C) :
    (1 - 16 * C ^ 2 / r ^ 2) * (p - r) <=
        cubicReciprocalTransport r p - cubicReciprocalTransport r r /\
      cubicReciprocalTransport r p - cubicReciprocalTransport r r <= p - r := by
  have hp : 0 < p := hr.trans_le hrp
  have hrelative : r * (p - r) <= 4 * C * p := by
    have h1 := mul_le_mul_of_nonneg_left hgap hr.le
    have h2 := mul_le_mul_of_nonneg_left hrp (by positivity : 0 <= 4 * C)
    nlinarith only [h1, h2]
  have he := cubic_reciprocal_remainder_le r C p (p - r)
    hr hC hp (sub_nonneg.mpr hrp) hrelative
  rw [cubicReciprocalTransport_sub r p hr.ne' hp.ne']
  simp only [div_eq_mul_inv] at he
  simp only [div_eq_mul_inv]
  constructor <;> nlinarith only [he.1, he.2]

/-- Leaving and entering coordinates use the same signed comparison. -/
theorem cubicReciprocalTransport_leaving_bounds (r p C : Real)
    (hr : 0 < r) (hC : 0 <= C) (hpr : p <= r) (hgap : r - p <= C)
    (hbudget : 4 * C < r) :
    (1 - 16 * C ^ 2 / r ^ 2) * (r - p) <=
        cubicReciprocalTransport r r - cubicReciprocalTransport r p /\
      cubicReciprocalTransport r r - cubicReciprocalTransport r p <= r - p := by
  have hp : 0 < p := by linarith only [hC, hgap, hbudget]
  have hrelative : r * (r - p) <= 4 * C * p := by
    have h1 := mul_le_mul_of_nonneg_left hgap hr.le
    have h2 := mul_nonneg hC (by linarith only [hr, hgap, hbudget] : 0 <= 4 * p - r)
    nlinarith only [h1, h2]
  have he := cubic_reciprocal_remainder_le r C p (r - p)
    hr hC hp (sub_nonneg.mpr hpr) hrelative
  have hid : cubicReciprocalTransport r r - cubicReciprocalTransport r p =
      (r - p) - (r - p) ^ 3 / p ^ 2 := by
    unfold cubicReciprocalTransport
    field_simp [hr.ne', hp.ne']
    ring
  rw [hid]
  simp only [div_eq_mul_inv] at he
  simp only [div_eq_mul_inv]
  constructor <;> nlinarith only [he.1, he.2]

end Real
