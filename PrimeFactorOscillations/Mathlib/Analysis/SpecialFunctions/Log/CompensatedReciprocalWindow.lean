/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocalCoercivity

/-!
# A sharper reciprocal window from integrated boundary costs

The window retains the exact incoming and outgoing costs at a quarter-reference
budget. Its rational left endpoint matches a Chebyshev characteristic root seven.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

/-- Integrated incoming cost places its reciprocal ratio above the half-square. -/
theorem incoming_quarter_cost_reciprocal_window (t r q C : Real)
    (ht : 0 < t) (hr : 0 < r) (hrq : r <= q) (hC : C < r / 4)
    (hcost : r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t r q <= C) :
    (1 / 2 : Real) < (r / q) ^ 2 /\ (45 / 64 : Real) <= r / q := by
  have hq := hr.trans_le hrq
  have hb := (incoming_integrated_normalized_pairLogDefect_lower t r q ht hr hrq).trans hcost
  have hratio : 0 <= r / q := by positivity
  have hs : (1 / 2 : Real) < (r / q) ^ 2 := by
    by_contra hn
    have hm := mul_nonneg hr.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith only [hb, hC, hm]
  refine And.intro hs ?_
  by_contra hn
  have hx : r / q < (45 / 64 : Real) := lt_of_not_ge hn
  nlinarith only [hx, hratio, hs]

/-- The exact outgoing comparison improves the reciprocal upper endpoint. -/
theorem outgoing_quarter_cost_reciprocal_window (t p r C : Real)
    (ht : 0 < t) (hp : 0 < p) (hpr : p <= r) (hC : C < r / 4)
    (hcost : r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t p r <= C) :
    r / p < (5 / 4 : Real) := by
  have hr := hp.trans_le hpr
  have hb := (outgoing_integrated_normalized_pairLogDefect_lower t p r ht hp hpr).trans hcost
  by_contra hn
  have hm := mul_nonneg hr.le (sub_nonneg.mpr (le_of_not_gt hn))
  nlinarith only [hb, hC, hm]

end Real
