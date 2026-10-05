/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Ring.ProductError

/-!
# Uniform linear approximation to a normalized falling factorial

The error is bounded uniformly in both natural parameters, including the
zero extension when the degree exceeds the initial value.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

private theorem range_cast_div_sum (r : Real) (hr : Not (r = 0)) (j : Nat) :
    (Finset.range j).sum (fun i => (i : Real) / r) =
      (j : Real) * (j - 1) / (2 * r) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring

private theorem normalized_descFactorial_eq_prod (r : Nat) (hr : 0 < r) :
    forall j : Nat, j <= r ->
      (r.descFactorial j : Real) / (r : Real) ^ j =
        (Finset.range j).prod (fun i => 1 - (i : Real) / r) := by
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  have hr0 : Not ((r : Real) = 0) := ne_of_gt hrR
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj
    have hjr : j <= r := (Nat.le_succ j).trans hj
    rw [Finset.prod_range_succ, <- ih hjr, descFactorial_succ,
      Nat.cast_mul, Nat.cast_sub hjr, pow_succ]
    field_simp

/-- A uniform quadratic-order bound for the normalized falling factorial,
including the zero extension beyond its degree. This is the finite error
estimate used when transferring an entire generating function to moving rank. -/
theorem descFactorial_normalized_linear_error_bounds (r j : Nat) (hr : 0 < r) :
    0 <= (r.descFactorial j : Real) / (r : Real) ^ j - 1 +
        (j : Real) * (j - 1) / (2 * r) /\
    (r.descFactorial j : Real) / (r : Real) ^ j - 1 +
        (j : Real) * (j - 1) / (2 * r) <= (j : Real) ^ 4 / (r : Real) ^ 2 := by
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  have hr0 : Not ((r : Real) = 0) := ne_of_gt hrR
  by_cases hj0 : j = 0
  next =>
    subst j
    simp
  have hjOne : (1 : Real) <= j := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
  have hjNonneg : (0 : Real) <= j := by positivity
  let T : Real := (j : Real) * (j - 1) / (2 * r)
  let Z : Real := (j : Real) ^ 2 / r
  have hT : 0 <= T := div_nonneg
    (mul_nonneg hjNonneg (sub_nonneg.mpr hjOne)) (by positivity)
  have hZ : 0 <= Z := div_nonneg (sq_nonneg _) hrR.le
  have hTZ : T <= Z := by
    have hnum : (j : Real) * (j - 1) / 2 <= (j : Real) ^ 2 := by
      nlinarith [sq_nonneg (j : Real)]
    calc
      T = ((j : Real) * (j - 1) / 2) / r := by
        dsimp [T]
        ring
      _ <= Z := div_le_div_of_nonneg_right hnum hrR.le
  have hZsq : Z ^ 2 = (j : Real) ^ 4 / (r : Real) ^ 2 := by
    dsimp [Z]
    rw [div_pow]
    ring
  by_cases hjr : j <= r
  next =>
    have hweights : forall i, Membership.mem (Finset.range j) i ->
        0 <= (i : Real) / r /\ (i : Real) / r <= 1 := by
      intro i hi
      have hir : i <= r := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hjr
      have hirR : (i : Real) <= r := by exact_mod_cast hir
      exact And.intro (div_nonneg (by positivity) hrR.le)
        ((div_le_one hrR).mpr hirR)
    have hfinite := Finset.prod_one_sub_linear_error_bounds
      (Finset.range j) (fun i => (i : Real) / r) hweights
    rw [<- normalized_descFactorial_eq_prod r hr j hjr,
      range_cast_div_sum (r : Real) hr0 j] at hfinite
    refine And.intro hfinite.1 (hfinite.2.trans ?_)
    change T ^ 2 / 2 <= (j : Real) ^ 4 / (r : Real) ^ 2
    rw [<- hZsq]
    have hsquare : T ^ 2 <= Z ^ 2 := by nlinarith
    nlinarith [sq_nonneg T]
  next =>
    have hlt : r < j := Nat.lt_of_not_ge hjr
    have hzero : r.descFactorial j = 0 := descFactorial_of_lt hlt
    rw [hzero, Nat.cast_zero, zero_div]
    have hjrR : (r : Real) + 1 <= j := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hjTwo : (2 : Real) <= j := by
      have hrOne : (1 : Real) <= r := by exact_mod_cast hr
      linarith
    have hTone : 1 <= T := by
      dsimp [T]
      apply (one_le_div (by positivity)).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hjOne) (sub_nonneg.mpr hjTwo)]
    have hZone : 1 <= Z := by
      dsimp [Z]
      apply (one_le_div hrR).mpr
      nlinarith [sq_nonneg ((j : Real) - 1)]
    simp only [zero_sub]
    change 0 <= -1 + T /\ -1 + T <= (j : Real) ^ 4 / (r : Real) ^ 2
    rw [<- hZsq]
    constructor
    next => linarith
    next => nlinarith [mul_nonneg hZ (sub_nonneg.mpr hZone)]

end Nat
