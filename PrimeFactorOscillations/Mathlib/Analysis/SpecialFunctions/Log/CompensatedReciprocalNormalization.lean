/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocal

/-!
# Uniform normalization of the compensated logarithmic boundary cost

The bound is uniform over every positive probe, even when the probe grows
or tends to zero with the reciprocal coordinate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

/-- Increasing reciprocal denominators give strictly increasing log weights. -/
theorem bernoulliLogProfile_strictMonoOn_pos (t : Real) (ht : 0 < t) :
    StrictMonoOn (bernoulliLogProfile t) (Set.Ioi 0) := by
  intro p hp q hq hpq
  change 0 < p at hp
  change 0 < q at hq
  have hdiff : 0 < q - p := sub_pos.mpr hpq
  have hb := (pairLogDefect_bounds t p q ht.le hp hq).1
  have hpos : 0 < t ^ 2 * (q - p) / (p * q * (q + t)) := by positivity
  exact sub_pos.mp (hpos.trans_le hb)

/-- One unit of denominator displacement costs at least a quarter after
normalization, uniformly over all positive probes and adjacent ratios <= 2. -/
theorem quarter_le_normalized_pairLogDefect (t p q : Real) (ht : 0 < t)
    (hp : 0 < p) (hg : 1 <= q - p) (hq : q <= 2 * p) :
    (1 / 4 : Real) <= p ^ 2 * (p + t) / t ^ 2 * pairLogDefect t p q := by
  have hpq : p < q := by linarith only [hg]
  have hqpos : 0 < q := hp.trans hpq
  have hqt : q + t <= 2 * (p + t) := by linarith only [hq, ht]
  have hm := mul_le_mul hq hqt (by positivity : 0 <= q + t)
    (by positivity : 0 <= 2 * p)
  have hden : p * q * (q + t) <= 4 * p ^ 2 * (p + t) := by
    nlinarith only [mul_le_mul_of_nonneg_left hm hp.le]
  have hnum : t ^ 2 <= t ^ 2 * (q - p) := by
    nlinarith only [mul_le_mul_of_nonneg_left hg (sq_nonneg t)]
  have hlo : t ^ 2 / (4 * p ^ 2 * (p + t)) <= pairLogDefect t p q := by
    calc
      _ <= t ^ 2 / (p * q * (q + t)) :=
        div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) hden
      _ <= t ^ 2 * (q - p) / (p * q * (q + t)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ <= _ := (pairLogDefect_bounds t p q ht.le hp hqpos).1
  have hnorm : 0 <= p ^ 2 * (p + t) / t ^ 2 := by positivity
  have heq : p ^ 2 * (p + t) / t ^ 2 *
      (t ^ 2 / (4 * p ^ 2 * (p + t))) = (1 / 4 : Real) := by
    field_simp [hp.ne', ht.ne', (add_pos hp ht).ne']
  rw [<- heq]
  exact mul_le_mul_of_nonneg_left hlo hnorm

end Real
