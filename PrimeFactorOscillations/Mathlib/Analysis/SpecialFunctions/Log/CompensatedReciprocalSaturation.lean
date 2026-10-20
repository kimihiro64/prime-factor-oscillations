/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocalNormalization

/-!
# Exact saturation of a fixed compensated logarithmic probe

The positive saturation and its rational residual control how far a coordinate
can enter below a fixed-probe budget. The probe is held fixed throughout.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

/-- A positive denominator has a strictly negative compensated log profile. -/
theorem neg_bernoulliLogProfile_bounds (t x : Real) (ht : 0 < t) (hx : 0 < x) :
    0 < -bernoulliLogProfile t x /\
      -bernoulliLogProfile t x <= t ^ 2 / (x * (x + t)) := by
  have hu : 0 < 1 + t / x := by positivity
  have hneq : Not (1 + t / x = 1) := by
    have hp : 0 < t / x := div_pos ht hx
    linarith only [hp]
  have hl := Real.log_lt_sub_one_of_pos hu hneq
  have hi := Real.log_le_sub_one_of_pos
    (by positivity : 0 < 1 / (1 + t / x))
  rw [one_div, Real.log_inv] at hi
  have hid : (1 + t / x) ^ (-1 : Int) - 1 + t / x =
      t ^ 2 / (x * (x + t)) := by
    simp only [zpow_neg_one]
    field_simp [hx.ne', (add_pos hx ht).ne']
    <;> ring
  constructor
  . unfold bernoulliLogProfile
    linarith only [hl]
  . unfold bernoulliLogProfile
    rw [<- hid]
    simp only [zpow_neg_one]
    linarith only [hi]

/-- The complete saturation value for one positive probe and reference. -/
def normalizedLogBoundarySaturation (t r : Real) : Real :=
  r ^ 2 * (r + t) / t ^ 2 * (-bernoulliLogProfile t r)

/-- Fixed-probe saturation is positive on the full admissible domain. -/
theorem normalizedLogBoundarySaturation_pos (t r : Real) (ht : 0 < t) (hr : 0 < r) :
    0 < normalizedLogBoundarySaturation t r := by
  exact mul_pos (by positivity) (neg_bernoulliLogProfile_bounds t r ht hr).1

/-- The exact saturation residual is positive and has an explicit rational tail. -/
theorem normalizedLogBoundarySaturation_residual_bounds (t r q : Real)
    (ht : 0 < t) (hr : 0 < r) (hq : 0 < q) :
    0 < normalizedLogBoundarySaturation t r -
        r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t r q /\
      normalizedLogBoundarySaturation t r -
        r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t r q <=
          r ^ 2 * (r + t) / (q * (q + t)) := by
  have hb := neg_bernoulliLogProfile_bounds t q ht hq
  have hc : 0 < r ^ 2 * (r + t) / t ^ 2 := by positivity
  have hid : normalizedLogBoundarySaturation t r -
      r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t r q =
      r ^ 2 * (r + t) / t ^ 2 * (-bernoulliLogProfile t q) := by
    unfold normalizedLogBoundarySaturation pairLogDefect
    ring
  rw [hid]
  refine And.intro (mul_pos hc hb.1) ?_
  calc
    _ <= r ^ 2 * (r + t) / t ^ 2 * (t ^ 2 / (q * (q + t))) :=
      mul_le_mul_of_nonneg_left hb.2 hc.le
    _ = r ^ 2 * (r + t) / (q * (q + t)) := by
      field_simp [ht.ne', hq.ne', (add_pos hq ht).ne']

/-- Below saturation a fixed-probe budget gives a quadratic coordinate constraint. -/
theorem incoming_coordinate_bound_of_cost_lt_saturation (t r q C : Real)
    (ht : 0 < t) (hr : 0 < r) (hq : 0 < q)
    (hC : C < normalizedLogBoundarySaturation t r)
    (hcost : r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t r q <= C) :
    (normalizedLogBoundarySaturation t r - C) * q * (q + t) <= r ^ 2 * (r + t) := by
  have hb := (normalizedLogBoundarySaturation_residual_bounds t r q ht hr hq).2
  have hleft : normalizedLogBoundarySaturation t r - C <=
      normalizedLogBoundarySaturation t r -
        r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t r q := by linarith only [hcost]
  have hm := mul_le_mul_of_nonneg_right (hleft.trans hb)
    (by positivity : 0 <= q * (q + t))
  have hid : r ^ 2 * (r + t) / (q * (q + t)) * (q * (q + t)) =
      r ^ 2 * (r + t) := by field_simp [hq.ne', (add_pos hq ht).ne']
  rw [hid] at hm
  nlinarith only [hm]

end Real
