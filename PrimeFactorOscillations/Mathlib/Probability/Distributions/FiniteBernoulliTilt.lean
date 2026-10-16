/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliPatterns

/-!
# Finite Bernoulli tilting and support-degree normalization

The exact coefficient tilting identity reuses the finite Bernoulli coefficient
library. Positive real tilts preserve the probability interval, including zero
and one coordinates. Finite exceptional-coordinate generating products are
normalized by the number of nonzero coordinates; their limit is the product of
those coordinates. Two normalized products therefore have the leading
coefficient ratio as their limit.

These are finite algebraic and finite-product limit results. No growing-array
local limit estimate or maximization theorem is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace List

/-- Exact exponential tilting of every finite Bernoulli coefficient. -/
theorem bernoulliMass_tilt {R : Type*} [Field R] (s : List R) (z : R)
    (r : Nat) (h : forall a, List.Mem a s -> Not (1 - a + a * z = 0)) :
    (s.map (fun a => 1 - a + a * z)).prod *
        bernoulliMass (s.map (fun a => a * z / (1 - a + a * z))) r =
      z ^ r * bernoulliMass s r := by
  revert h
  induction s generalizing r with
  | nil => intro h; cases r <;> simp [bernoulliMass]
  | cons a s ih =>
    intro h
    have ha := h a mem_cons_self
    have hs : forall b, List.Mem b s -> Not (1 - b + b * z = 0) :=
      fun b hb => h b (mem_cons_of_mem a hb)
    have hsuccess : (1 - a + a * z) * (a * z / (1 - a + a * z)) = a * z := by
      field_simp
    have hfailure : (1 - a + a * z) * (1 - a * z / (1 - a + a * z)) = 1 - a := by
      field_simp
      ring
    cases r with
    | zero =>
      simp only [map_cons, prod_cons, bernoulliMass]
      calc
        _ = ((1 - a + a * z) * (1 - a * z / (1 - a + a * z))) *
          ((s.map (fun b => 1 - b + b * z)).prod *
            bernoulliMass (s.map (fun b => b * z / (1 - b + b * z))) 0) := by ring
        _ = (1 - a) * (z ^ 0 * bernoulliMass s 0) := by rw [hfailure, ih 0 hs]
        _ = _ := by ring
    | succ r =>
      simp only [map_cons, prod_cons, bernoulliMass]
      calc
        _ = ((1 - a + a * z) * (1 - a * z / (1 - a + a * z))) *
            ((s.map (fun b => 1 - b + b * z)).prod *
              bernoulliMass (s.map (fun b => b * z / (1 - b + b * z))) (r + 1)) +
          ((1 - a + a * z) * (a * z / (1 - a + a * z))) *
            ((s.map (fun b => 1 - b + b * z)).prod *
              bernoulliMass (s.map (fun b => b * z / (1 - b + b * z))) r) := by ring
        _ = (1 - a) * (z ^ (r + 1) * bernoulliMass s (r + 1)) +
            (a * z) * (z ^ r * bernoulliMass s r) := by
          rw [hfailure, hsuccess, ih (r + 1) hs, ih r hs]
        _ = _ := by rw [pow_succ]; ring

/-- Every Bernoulli factor is strictly positive at a positive real tilt,
including an excluded or forced coordinate. -/
theorem bernoulliFactor_pos (a z : Real) (ha0 : 0 <= a) (ha1 : a <= 1)
    (hz : 0 < z) : 0 < 1 - a + a * z := by
  by_cases ha : a = 0
  next => simp [ha]
  next =>
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ha1)
      (mul_pos (lt_of_le_of_ne ha0 (Ne.symm ha)) hz)

/-- A positive tilt preserves the probability interval without excluding
deterministic coordinates. -/
theorem bernoulliTilt_mem_unitInterval (a z : Real) (ha0 : 0 <= a) (ha1 : a <= 1)
    (hz : 0 < z) :
    0 <= a * z / (1 - a + a * z) /\
      a * z / (1 - a + a * z) <= 1 := by
  have hf := bernoulliFactor_pos a z ha0 ha1 hz
  constructor
  next => exact div_nonneg (mul_nonneg ha0 hz.le) hf.le
  next =>
    apply (div_le_one hf).mpr
    exact le_add_of_nonneg_left (sub_nonneg.mpr ha1)

/-- Removing excluded coordinates gives the exact degree normalization. -/
theorem bernoulliProduct_normalized {R : Type*} [Field R] [DecidableEq R]
    (s : List R) (z : R) (hz : Not (z = 0)) :
    (s.map (fun a => 1 - a + a * z)).prod /
        z ^ (s.filter (fun a => decide (Not (a = 0)))).length =
      ((s.filter (fun a => decide (Not (a = 0)))).map
        (fun a => a + (1 - a) / z)).prod := by
  induction s with
  | nil => simp
  | cons a s ih =>
    by_cases ha : a = 0
    next =>
      subst a
      simpa using ih
    next =>
      have hf : (a :: s).filter (fun a => decide (Not (a = 0))) =
          a :: s.filter (fun a => decide (Not (a = 0))) := by simp [ha]
      rw [hf]
      simp only [map_cons, prod_cons, length_cons, pow_succ]
      calc
        _ = (a + (1 - a) / z) *
          ((s.map (fun b => 1 - b + b * z)).prod /
            z ^ (s.filter (fun b => decide (Not (b = 0)))).length) := by
          field_simp
          ring
        _ = _ := by rw [ih]

/-- The leading coefficient is positive when all nonexcluded coordinates are
nonnegative. This includes an empty support and forced coordinates. -/
theorem bernoulliSupport_prod_pos (s : List Real)
    (h : forall a, List.Mem a s -> 0 <= a) :
    0 < (s.filter (fun a => decide (Not (a = 0)))).prod := by
  revert h
  induction s with
  | nil => intro h; simp
  | cons a s ih =>
    intro h
    have hs : forall b, List.Mem b s -> 0 <= b :=
      fun b hb => h b (mem_cons_of_mem a hb)
    by_cases ha : a = 0
    next =>
      subst a
      simpa using ih hs
    next =>
      have hf : (a :: s).filter (fun a => decide (Not (a = 0))) =
          a :: s.filter (fun a => decide (Not (a = 0))) := by simp [ha]
      rw [hf, prod_cons]
      exact mul_pos (lt_of_le_of_ne (h a mem_cons_self) (Ne.symm ha)) (ih hs)

/-- At a growing positive tilt the finite exceptional-coordinate product has
degree equal to its nonzero support, rather than its forced-coordinate count. -/
theorem tendsto_bernoulliProduct_normalized (s : List Real) :
    Filter.Tendsto
      (fun z : Real => (s.map (fun a => 1 - a + a * z)).prod /
        z ^ (s.filter (fun a => decide (Not (a = 0)))).length)
      Filter.atTop (nhds (s.filter (fun a => decide (Not (a = 0)))).prod) := by
  have hlimit (t : List Real) :
      Filter.Tendsto (fun z : Real => (t.map (fun a => a + (1 - a) / z)).prod)
        Filter.atTop (nhds t.prod) := by
    induction t with
    | nil => simp
    | cons a t ih =>
      have hc : Filter.Tendsto (fun _ : Real => 1 - a)
          Filter.atTop (nhds (1 - a)) := tendsto_const_nhds
      have hz : Filter.Tendsto (fun z : Real => (1 - a) / z)
          Filter.atTop (nhds 0) := by
        simpa only [div_eq_mul_inv, mul_zero] using hc.mul tendsto_inv_atTop_zero
      have ha : Filter.Tendsto (fun _ : Real => a) Filter.atTop (nhds a) :=
        tendsto_const_nhds
      have hf : Filter.Tendsto (fun z : Real => a + (1 - a) / z)
          Filter.atTop (nhds a) := by simpa only [add_zero] using ha.add hz
      simpa only [map_cons, prod_cons] using hf.mul ih
  apply (hlimit (s.filter (fun a => decide (Not (a = 0))))).congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with z hz
  exact (bernoulliProduct_normalized s z (ne_of_gt hz)).symm

/-- Two finite exceptional-coordinate products contribute exactly their leading
coefficient ratio after each has been divided by its support-degree power. -/
theorem tendsto_bernoulliProduct_normalized_ratio (s t : List Real)
    (ht : forall a, List.Mem a t -> 0 <= a) :
    Filter.Tendsto
      (fun z : Real =>
        ((s.map (fun a => 1 - a + a * z)).prod /
          z ^ (s.filter (fun a => decide (Not (a = 0)))).length) /
        ((t.map (fun a => 1 - a + a * z)).prod /
          z ^ (t.filter (fun a => decide (Not (a = 0)))).length))
      Filter.atTop (nhds
        ((s.filter (fun a => decide (Not (a = 0)))).prod /
          (t.filter (fun a => decide (Not (a = 0)))).prod)) :=
  (tendsto_bernoulliProduct_normalized s).div
    (tendsto_bernoulliProduct_normalized t) (ne_of_gt (bernoulliSupport_prod_pos t ht))

end List
