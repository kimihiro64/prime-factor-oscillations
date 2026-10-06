/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasMomentConsumer

/-!
# The precise loss of the fixed second-moment envelope

The positive-part quadratic majorant is valid, but its square-root area
scale exceeds the quarter-power target by an unbounded factor. This only
limits that specific envelope and is not a lower bound for actual area.
-/

set_option autoImplicit false
set_option Elab.async false
namespace PrimeFactorOscillations
open Filter

theorem positive_part_le_second_moment_envelope (v m : Real) (hm : 0 < m) :
    max (v - m) 0 <= v ^ 2 / (4 * m) := by
  by_cases hv : v <= m
  . rw [max_eq_right (by linarith)]
    positivity
  . rw [max_eq_left (by linarith)]
    have hd : 0 < 4 * m := by positivity
    have hc : (v ^ 2 / (4 * m)) * (4 * m) = v ^ 2 := by field_simp
    by_contra hn
    have ht := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hd
    rw [hc] at ht
    nlinarith only [sq_nonneg (v - 2 * m), ht]

/-- This compares two proposed envelopes; it is not a lower bound on actual area. -/
theorem second_moment_area_envelope_ratio_diverges :
    Tendsto (fun x : Real =>
      (x ^ (1 / 2 : Real) / Real.log x) /
        (x ^ (1 / 4 : Real) / Real.log x)) atTop atTop := by
  have he : Filter.EventuallyEq atTop
      (fun x : Real => (x ^ (1 / 2 : Real) / Real.log x) /
        (x ^ (1 / 4 : Real) / Real.log x))
      (fun x : Real => x ^ (1 / 4 : Real)) := by
    filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hl : Not (Real.log x = 0) := (Real.log_pos hx).ne'
    have hp : Not (x ^ (1 / 4 : Real) = 0) := (Real.rpow_pos_of_pos hx0 _).ne'
    have hSquare : x ^ (1 / 4 : Real) * x ^ (1 / 4 : Real) = x ^ (1 / 2 : Real) := by
      rw [<- Real.rpow_add hx0]
      norm_num
    rw [<- hSquare]
    field_simp
  exact (tendsto_congr' he).mpr (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 4))

end PrimeFactorOscillations


