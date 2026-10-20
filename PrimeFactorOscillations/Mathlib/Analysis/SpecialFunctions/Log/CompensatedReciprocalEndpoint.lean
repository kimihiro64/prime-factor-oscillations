/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocalSaturation

/-!
# A sharp endpoint envelope for compensated logarithmic deficits

A quadratic logarithmic lower envelope has a square derivative. It bounds
every positive probe by a convex combination of its two rational endpoints.
Explicit small- and large-probe lower bounds approach those endpoints.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

/-- A parameterized logarithmic lower envelope with a square derivative. -/
theorem log_one_add_quadratic_parameter_lower (u z : Real) (hz : 0 <= z) :
    (1 + 2 * u) * z - z ^ 2 / 2 <= (1 + u) ^ 2 * Real.log (1 + z) := by
  let F := fun x : Real => (1 + u) ^ 2 * Real.log (1 + x) -
    (1 + 2 * u) * x + x ^ 2 / 2
  let dF := fun x : Real => (x - u) ^ 2 / (1 + x)
  have hder : forall x : Real, 0 <= x -> HasDerivAt F (dF x) x := by
    intro x hx
    have h1 : 0 < 1 + x := by linarith only [hx]
    have hl := ((hasDerivAt_id x).const_add 1).log h1.ne'
    have hd := ((hl.const_mul ((1 + u) ^ 2)).sub
      ((hasDerivAt_id x).const_mul (1 + 2 * u))).add
      (((hasDerivAt_id x).pow 2).div (hasDerivAt_const x (2 : Real)) (by norm_num))
    convert hd using 1
    . dsimp [F]
      rfl
    . dsimp [dF]
      field_simp [h1.ne']
      ring
  have hcont : ContinuousOn F (Set.Icc 0 z) := by
    intro x hx
    exact (hder x hx.1).continuousAt.continuousWithinAt
  have hmono : MonotoneOn F (Set.Icc 0 z) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 z) hcont
      (fun x hx => (hder x (interior_subset hx).1).hasDerivWithinAt)
      (by
        intro x hx
        have hxp := (interior_subset hx).1
        dsimp only [dF]
        exact div_nonneg (sq_nonneg _) (by linarith only [hxp]))
  have h := hmono (Set.left_mem_Icc.mpr hz) (Set.right_mem_Icc.mpr hz) hz
  have hzero : F 0 = 0 := by simp [F]
  rw [hzero] at h
  dsimp only [F] at h
  linarith only [h]

/-- The complementary rational lower bound on the complete logarithmic deficit. -/
theorem log_deficit_quadratic_fraction_lower (z : Real) (hz : 0 <= z) :
    z ^ 2 / (2 * (1 + z)) <= z - Real.log (1 + z) := by
  let F := fun x : Real => x - Real.log (1 + x) - x ^ 2 / (2 * (1 + x))
  let dF := fun x : Real => x ^ 2 / (2 * (1 + x) ^ 2)
  have hder : forall x : Real, 0 <= x -> HasDerivAt F (dF x) x := by
    intro x hx
    have h1 : 0 < 1 + x := by linarith only [hx]
    have hl := ((hasDerivAt_id x).const_add 1).log h1.ne'
    have hd := ((hasDerivAt_id x).sub hl).sub
      (((hasDerivAt_id x).pow 2).div
        (((hasDerivAt_id x).const_add 1).const_mul 2) (by positivity))
    convert hd using 1
    . dsimp [F]
      rfl
    . dsimp [dF]
      field_simp [h1.ne']
      ring
  have hcont : ContinuousOn F (Set.Icc 0 z) := by
    intro x hx
    exact (hder x hx.1).continuousAt.continuousWithinAt
  have hmono : MonotoneOn F (Set.Icc 0 z) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 z) hcont
      (fun x hx => (hder x (interior_subset hx).1).hasDerivWithinAt)
      (by
        intro x hx
        dsimp only [dF]
        positivity)
  have h := hmono (Set.left_mem_Icc.mpr hz) (Set.right_mem_Icc.mpr hz) hz
  have hzero : F 0 = 0 := by simp [F]
  rw [hzero] at h
  dsimp only [F] at h
  linarith only [h]

/-- A positive raw coordinate deficit normalized at an independent positive reference. -/
def normalizedLogDeficit (t r p : Real) : Real :=
  r ^ 2 * (r + t) / t ^ 2 * (-bernoulliLogProfile t p)

/-- Every positive probe lies below one convex combination of the two rational endpoints. -/
theorem normalizedLogDeficit_le_endpoint_convex (t r p : Real)
    (ht : 0 < t) (hr : 0 < r) (hp : 0 < p) :
    normalizedLogDeficit t r p <=
      r / (r + t) * (r ^ 3 / (2 * p ^ 2)) +
        t / (r + t) * (r ^ 2 / p) := by
  have h := log_one_add_quadratic_parameter_lower (t / r) (t / p) (by positivity)
  have hm := mul_nonneg (by positivity : 0 <= r ^ 4 / (t ^ 2 * (r + t)))
    (sub_nonneg.mpr h)
  have hid : r ^ 4 / (t ^ 2 * (r + t)) *
      ((1 + t / r) ^ 2 * Real.log (1 + t / p) -
        ((1 + 2 * (t / r)) * (t / p) - (t / p) ^ 2 / 2)) =
      r / (r + t) * (r ^ 3 / (2 * p ^ 2)) +
        t / (r + t) * (r ^ 2 / p) - normalizedLogDeficit t r p := by
    unfold normalizedLogDeficit bernoulliLogProfile
    field_simp [hr.ne', ht.ne', hp.ne', (add_pos hr ht).ne']
    ring
  rw [hid] at hm
  exact sub_nonneg.mp hm

/-- A linear error in a small positive probe retains the entire quadratic endpoint. -/
theorem normalizedLogDeficit_small_probe_lower (t r p : Real)
    (ht : 0 < t) (hr : 0 < r) (hp : 0 < p) :
    r ^ 3 / (2 * p ^ 2) - t * (r ^ 3 / (2 * p ^ 3)) <=
      normalizedLogDeficit t r p := by
  have h := mul_le_mul_of_nonneg_left
    (log_deficit_quadratic_fraction_lower (t / p) (by positivity))
    (by positivity : 0 <= r ^ 2 * (r + t) / t ^ 2)
  have hid : r ^ 2 * (r + t) / t ^ 2 *
      ((t / p) ^ 2 / (2 * (1 + t / p))) =
        r ^ 2 * (r + t) / (2 * p * (p + t)) := by
    field_simp [ht.ne', hp.ne', (add_pos hp ht).ne']
  rw [hid] at h
  have hlow : r ^ 2 * (r + t) / (2 * p * (p + t)) <=
      normalizedLogDeficit t r p := by
    simpa only [normalizedLogDeficit, bernoulliLogProfile, neg_sub] using h
  have hgap : r ^ 2 * (r + t) / (2 * p * (p + t)) -
      (r ^ 3 / (2 * p ^ 2) - t * (r ^ 3 / (2 * p ^ 3))) =
        r ^ 2 * t * (p ^ 2 + r * t) / (2 * p ^ 3 * (p + t)) := by
    field_simp [hp.ne', (add_pos hp ht).ne']
    ring
  have hpos : 0 <= r ^ 2 * t * (p ^ 2 + r * t) / (2 * p ^ 3 * (p + t)) := by
    positivity
  linarith only [hlow, hgap, hpos]

/-- An explicit tangent parameter gives a lower estimate near the large-probe endpoint. -/
theorem normalizedLogDeficit_large_probe_lower (t r p a : Real)
    (ht : 0 < t) (hr : 0 < r) (hp : 0 < p) (ha : 1 <= a) :
    (1 - 1 / a) * (r ^ 2 / p) - r ^ 2 * a / t <=
      normalizedLogDeficit t r p := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hx : 0 < 1 + t / p := by positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hx ha0)
  rw [Real.log_div hx.ne' ha0.ne'] at hl
  have hla := Real.log_le_sub_one_of_pos ha0
  have hi : 1 / a <= 1 := (div_le_one ha0).mpr ha
  have hid1 : (1 + t / p) / a = 1 / a + t / (a * p) := by
    field_simp [ha0.ne', hp.ne']
  rw [hid1] at hl
  have hlog : Real.log (1 + t / p) <= a + t / (a * p) := by
    linarith only [hl, hla, hi]
  have hb := (neg_bernoulliLogProfile_bounds t p ht hp).1
  have hpos : 0 <= r ^ 3 / t ^ 2 * (-bernoulliLogProfile t p) := by
    exact mul_nonneg (by positivity) hb.le
  have hdef : normalizedLogDeficit t r p =
      r ^ 2 / p - r ^ 2 / t * Real.log (1 + t / p) +
        r ^ 3 / t ^ 2 * (-bernoulliLogProfile t p) := by
    unfold normalizedLogDeficit bernoulliLogProfile
    field_simp [ht.ne', hp.ne']
    ring
  have hm := mul_le_mul_of_nonneg_left hlog (by positivity : 0 <= r ^ 2 / t)
  have hid2 : r ^ 2 / p - r ^ 2 / t * (a + t / (a * p)) =
      (1 - 1 / a) * (r ^ 2 / p) - r ^ 2 * a / t := by
    field_simp [ht.ne', hp.ne', ha0.ne']
    ring
  rw [<- hid2]
  linarith only [hdef, hpos, hm]

end Real
