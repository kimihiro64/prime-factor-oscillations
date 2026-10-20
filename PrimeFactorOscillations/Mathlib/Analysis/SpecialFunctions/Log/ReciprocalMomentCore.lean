/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CubicReciprocalTransport

/-!
# Exact finite reciprocal-moment compensation

A centered polynomial of degree m in the reciprocal probability has unit
displacement response with an exact remainder of order m+1. A relative
displacement bound controls that complete remainder at every order.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

/-- A degree-m polynomial in the reciprocal probability 1/p. -/
def reciprocalMomentTransport (m : Nat) (r p : Real) : Real :=
  r * (Finset.range m).sum (fun j => (1 - r / p) ^ (j + 1))

/-- The complete finite geometric cancellation, with no asymptotic remainder. -/
theorem reciprocalMomentTransport_eq (m : Nat) (r p : Real)
    (hp : Not (p = 0)) :
    reciprocalMomentTransport m r p =
      (p - r) - (p - r) ^ (m + 1) / p ^ m := by
  induction m with
  | zero =>
      simp [reciprocalMomentTransport]
  | succ m ih =>
      have hstep : reciprocalMomentTransport (m + 1) r p =
          reciprocalMomentTransport m r p + r * (1 - r / p) ^ (m + 1) := by
        simp only [reciprocalMomentTransport, Finset.sum_range_succ, mul_add]
      rw [hstep, ih]
      have hx : 1 - r / p = (p - r) / p := by
        field_simp [hp]
      rw [hx, div_pow]
      simp only [pow_succ]
      field_simp [hp, pow_ne_zero m hp]
      ring

/-- The reference coordinate contributes exactly zero at every order. -/
theorem reciprocalMomentTransport_self (m : Nat) (r : Real)
    (hr : Not (r = 0)) : reciprocalMomentTransport m r r = 0 := by
  simp [reciprocalMomentTransport, hr]

/-- Preserve all powers of the relative displacement before summing. -/
theorem reciprocal_moment_remainder_le (m : Nat) (r C p x : Real)
    (hr : 0 < r) (hC : 0 <= C) (hp : 0 < p) (hx : 0 <= x)
    (hrelative : r * x <= 4 * C * p) :
    0 <= x ^ (m + 1) / p ^ m /\
      x ^ (m + 1) / p ^ m <= (4 * C / r) ^ m * x := by
  have hid : (4 * C / r - x / p) * (r * p) = 4 * C * p - r * x := by
    field_simp [hr.ne', hp.ne']
  have hratio : x / p <= 4 * C / r := by
    by_contra hn
    have hbad := mul_neg_of_neg_of_pos (sub_neg.mpr (lt_of_not_ge hn))
      (mul_pos hr hp)
    rw [hid] at hbad
    linarith only [hbad, hrelative]
  have hpowers : forall j : Nat, (x / p) ^ j <= (4 * C / r) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hratio (by positivity) (by positivity)
  have heq : x ^ (m + 1) / p ^ m = (x / p) ^ m * x := by
    rw [pow_succ, div_pow]
    ring
  refine And.intro (by positivity) ?_
  rw [heq]
  exact mul_le_mul_of_nonneg_right (hpowers m) hx

end Real
