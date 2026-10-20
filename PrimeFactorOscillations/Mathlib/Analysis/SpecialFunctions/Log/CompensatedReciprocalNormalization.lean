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

/-- A zero coordinate has divergent normalized cost: the estimate is uniform
over every positive probe, using only the signed p-to-2p comparison. -/
theorem quarter_denominator_le_normalized_zero_cost (t p : Real)
    (ht : 0 < t) (hp : 0 < p) :
    p / 4 <= p ^ 2 * (p + t) / t ^ 2 *
      (t / p - Real.log (1 + t / p)) := by
  have h2p : 0 < 2 * p := by positivity
  have hb := (pairLogDefect_bounds t p (2 * p) ht.le hp h2p).1
  have hden : p * (2 * p) * (2 * p + t) <= 4 * p ^ 2 * (p + t) := by
    nlinarith only [mul_nonneg (sq_nonneg p) ht.le]
  have hlow : t ^ 2 * p / (4 * p ^ 2 * (p + t)) <= pairLogDefect t p (2 * p) := by
    calc
      _ <= t ^ 2 * p / (p * (2 * p) * (2 * p + t)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = t ^ 2 * (2 * p - p) / (p * (2 * p) * (2 * p + t)) := by ring
      _ <= _ := hb
  have hlog := Real.log_le_sub_one_of_pos
    (by positivity : 0 < 1 + t / (2 * p))
  have hpair : pairLogDefect t p (2 * p) <=
      t / p - Real.log (1 + t / p) := by
    unfold pairLogDefect bernoulliLogProfile
    linarith only [hlog]
  have hn : 0 <= p ^ 2 * (p + t) / t ^ 2 := by positivity
  have heq : p ^ 2 * (p + t) / t ^ 2 *
      (t ^ 2 * p / (4 * p ^ 2 * (p + t))) = p / 4 := by
    field_simp [hp.ne', ht.ne', (add_pos hp ht).ne']
  rw [<- heq]
  exact mul_le_mul_of_nonneg_left (hlow.trans hpair) hn

/-- The sharp normalized boundary cost retains the complete displacement. -/
theorem gap_mul_ratio_sq_le_normalized_pairLogDefect (t p q : Real)
    (ht : 0 < t) (hp : 0 < p) (hpq : p <= q) :
    (q - p) * (p / q) ^ 2 <=
      p ^ 2 * (p + t) / t ^ 2 * pairLogDefect t p q := by
  have hq : 0 < q := hp.trans_le hpq
  have hnorm : 0 <= p ^ 2 * (p + t) / t ^ 2 := by positivity
  have hb := mul_le_mul_of_nonneg_left
    (pairLogDefect_bounds t p q ht.le hp hq).1 hnorm
  have heq : p ^ 2 * (p + t) / t ^ 2 *
      (t ^ 2 * (q - p) / (p * q * (q + t))) =
      (q - p) * p * (p + t) / (q * (q + t)) := by
    field_simp [hp.ne', hq.ne', ht.ne', (add_pos hq ht).ne']
  rw [heq] at hb
  have hid : ((q - p) * p * (p + t) / (q * (q + t)) -
      (q - p) * (p / q) ^ 2) * (q ^ 2 * (q + t)) =
      p * t * (q - p) ^ 2 := by
    field_simp [hq.ne', (add_pos hq ht).ne']
    ring
  have hcmp : (q - p) * (p / q) ^ 2 <=
      (q - p) * p * (p + t) / (q * (q + t)) := by
    by_contra hn
    have hneg : (q - p) * p * (p + t) / (q * (q + t)) -
        (q - p) * (p / q) ^ 2 < 0 := sub_neg.mpr (lt_of_not_ge hn)
    have hbad := mul_neg_of_neg_of_pos hneg
      (by positivity : 0 < q ^ 2 * (q + t))
    rw [hid] at hbad
    have hpos : 0 <= p * t * (q - p) ^ 2 := by positivity
    exact (not_lt_of_ge hpos) hbad
  exact hcmp.trans hb

/-- The matching sharp upper cost is uniform over every positive probe. -/
theorem normalized_pairLogDefect_le_gap_mul_ratio (t p q : Real)
    (ht : 0 < t) (hp : 0 < p) (hq : 0 < q) :
    p ^ 2 * (p + t) / t ^ 2 * pairLogDefect t p q <=
      (q - p) * (p / q) := by
  have hn : 0 <= p ^ 2 * (p + t) / t ^ 2 := by positivity
  calc
    _ <= p ^ 2 * (p + t) / t ^ 2 *
        (t ^ 2 * (q - p) / (p * q * (p + t))) :=
      mul_le_mul_of_nonneg_left (pairLogDefect_bounds t p q ht.le hp hq).2 hn
    _ = _ := by
      field_simp [hp.ne', hq.ne', ht.ne', (add_pos hp ht).ne']

/-- Bounded denominator displacement gives an explicit reciprocal-law error,
with the small-denominator cutoff retained. -/
theorem abs_reciprocal_difference_le_twice_gap (p q h : Real)
    (hp : 0 < p) (hq : 0 < q) (hgap : abs (p - q) <= h) (hcut : 2 * h <= p) :
    abs (1 / q - 1 / p) <= 2 * h / p ^ 2 := by
  have hh : 0 <= h := (abs_nonneg (p - q)).trans hgap
  have hqp : p <= 2 * q := by
    have hle : p - q <= h := (le_abs_self (p - q)).trans hgap
    linarith only [hle, hcut]
  have hden : p ^ 2 <= 2 * (p * q) := by
    nlinarith only [mul_le_mul_of_nonneg_left hqp hp.le]
  have heq : 1 / q - 1 / p = (p - q) / (p * q) := by
    field_simp [hp.ne', hq.ne']
  rw [heq, abs_div, abs_of_pos (mul_pos hp hq)]
  calc
    _ <= h / (p * q) :=
      div_le_div_of_nonneg_right hgap (mul_nonneg hp.le hq.le)
    _ = 2 * h / (2 * (p * q)) := by
      field_simp [hp.ne', hq.ne']
    _ <= _ := div_le_div_of_nonneg_left (by positivity) (pow_pos hp 2) hden

/-- A middle reference denominator preserves the sharp signed gap cost. -/
theorem gap_mul_reference_ratio_sq_le_normalized_pairLogDefect (t p q r : Real)
    (ht : 0 < t) (hp : 0 < p) (hpq : p <= q) (hpr : p <= r) :
    (q - p) * (r / q) ^ 2 <=
      r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t p q := by
  have hq : 0 < q := hp.trans_le hpq
  have hr : 0 < r := hp.trans_le hpr
  have hnorm : 0 <= r ^ 2 * (r + t) / t ^ 2 := by positivity
  have hb := mul_le_mul_of_nonneg_left
    (pairLogDefect_bounds t p q ht.le hp hq).1 hnorm
  have heq : r ^ 2 * (r + t) / t ^ 2 *
      (t ^ 2 * (q - p) / (p * q * (q + t))) =
      (q - p) * r ^ 2 * (r + t) / (p * q * (q + t)) := by
    field_simp [hp.ne', hq.ne', ht.ne', (add_pos hq ht).ne']
  rw [heq] at hb
  have hid : ((q - p) * r ^ 2 * (r + t) / (p * q * (q + t)) -
      (q - p) * (r / q) ^ 2) * (p * q ^ 2 * (q + t)) =
      (q - p) * r ^ 2 * (q * (r - p) + t * (q - p)) := by
    field_simp [hp.ne', hq.ne', (add_pos hq ht).ne']
    ring
  have hcmp : (q - p) * (r / q) ^ 2 <=
      (q - p) * r ^ 2 * (r + t) / (p * q * (q + t)) := by
    by_contra hn
    have hneg := sub_neg.mpr (lt_of_not_ge hn)
    have hbad := mul_neg_of_neg_of_pos hneg
      (by positivity : 0 < p * q ^ 2 * (q + t))
    rw [hid] at hbad
    have hcore : 0 <= q * (r - p) + t * (q - p) :=
      add_nonneg (mul_nonneg hq.le (sub_nonneg.mpr hpr))
        (mul_nonneg ht.le (sub_nonneg.mpr hpq))
    have hpos : 0 <= (q - p) * r ^ 2 * (q * (r - p) + t * (q - p)) :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hpq) (sq_nonneg r)) hcore
    exact (not_lt_of_ge hpos) hbad
  exact hcmp.trans hb

/-- The matching upper bound at a middle reference is uniform in the probe. -/
theorem normalized_pairLogDefect_le_gap_mul_reference_ratio_sq (t p q r : Real)
    (ht : 0 < t) (hp : 0 < p) (hpq : p <= q) (hpr : p <= r) (hrq : r <= q) :
    r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t p q <=
      (q - p) * (r / p) ^ 2 := by
  have hq : 0 < q := hp.trans_le hpq
  have hr : 0 < r := hp.trans_le hpr
  have hnorm : 0 <= r ^ 2 * (r + t) / t ^ 2 := by positivity
  have hb := mul_le_mul_of_nonneg_left
    (pairLogDefect_bounds t p q ht.le hp hq).2 hnorm
  have heq : r ^ 2 * (r + t) / t ^ 2 *
      (t ^ 2 * (q - p) / (p * q * (p + t))) =
      (q - p) * r ^ 2 * (r + t) / (p * q * (p + t)) := by
    field_simp [hp.ne', hq.ne', ht.ne', (add_pos hp ht).ne']
  rw [heq] at hb
  have hid : ((q - p) * (r / p) ^ 2 -
      (q - p) * r ^ 2 * (r + t) / (p * q * (p + t))) *
      (p ^ 2 * q * (p + t)) =
      (q - p) * r ^ 2 * (p * (q - r) + t * (q - p)) := by
    field_simp [hp.ne', hq.ne', (add_pos hp ht).ne']
    ring
  have hcmp : (q - p) * r ^ 2 * (r + t) / (p * q * (p + t)) <=
      (q - p) * (r / p) ^ 2 := by
    by_contra hn
    have hneg := sub_neg.mpr (lt_of_not_ge hn)
    have hbad := mul_neg_of_neg_of_pos hneg
      (by positivity : 0 < p ^ 2 * q * (p + t))
    rw [hid] at hbad
    have hcore : 0 <= p * (q - r) + t * (q - p) :=
      add_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hrq))
        (mul_nonneg ht.le (sub_nonneg.mpr hpq))
    have hpos : 0 <= (q - p) * r ^ 2 * (p * (q - r) + t * (q - p)) :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hpq) (sq_nonneg r)) hcore
    exact (not_lt_of_ge hpos) hbad
  exact hb.trans hcmp

end Real
