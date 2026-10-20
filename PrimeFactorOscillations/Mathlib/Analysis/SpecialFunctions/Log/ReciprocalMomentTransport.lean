/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.ReciprocalMomentCore

/-!
# Finite reciprocal-moment compensation of arbitrary order

A centered polynomial of degree m in the reciprocal probability has unit
displacement response with an exact remainder of order m+1. Even orders
give nonnegative remainders on both sides of the reference and retain
the same relative-displacement bound for the full signed transport.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

/-- Every order has the same relative lower comparison on entering coordinates. -/
theorem reciprocalMomentTransport_entering_bounds (m : Nat) (r p C : Real)
    (hr : 0 < r) (hC : 0 <= C) (hrp : r <= p) (hgap : p - r <= 4 * C) :
    (1 - (4 * C / r) ^ m) * (p - r) <= reciprocalMomentTransport m r p /\
      reciprocalMomentTransport m r p <= p - r := by
  have hp : 0 < p := hr.trans_le hrp
  have hrelative : r * (p - r) <= 4 * C * p := by
    have h1 := mul_le_mul_of_nonneg_left hgap hr.le
    have h2 := mul_le_mul_of_nonneg_left hrp (by positivity : 0 <= 4 * C)
    nlinarith only [h1, h2]
  have he := reciprocal_moment_remainder_le m r C p (p - r)
    hr hC hp (sub_nonneg.mpr hrp) hrelative
  rw [reciprocalMomentTransport_eq m r p hp.ne']
  constructor <;> nlinarith only [he.1, he.2]

/-- An even order gives the matching sign on every leaving coordinate. -/
theorem reciprocalMomentTransport_leaving_bounds (k : Nat) (r p C : Real)
    (hr : 0 < r) (hC : 0 <= C) (hpr : p <= r) (hgap : r - p <= C)
    (hbudget : 4 * C < r) :
    (1 - (4 * C / r) ^ (2 * k)) * (r - p) <=
        -reciprocalMomentTransport (2 * k) r p /\
      -reciprocalMomentTransport (2 * k) r p <= r - p := by
  have hp : 0 < p := by linarith only [hC, hgap, hbudget]
  have hrelative : r * (r - p) <= 4 * C * p := by
    have h1 := mul_le_mul_of_nonneg_left hgap hr.le
    have h2 := mul_nonneg hC (by linarith only [hr, hgap, hbudget] : 0 <= 4 * p - r)
    nlinarith only [h1, h2]
  have he := reciprocal_moment_remainder_le (2 * k) r C p (r - p)
    hr hC hp (sub_nonneg.mpr hpr) hrelative
  have heven : (p - r) ^ (2 * k) = (r - p) ^ (2 * k) := by
    rw [pow_mul, pow_mul]
    congr 1
    ring
  have hodd : (p - r) ^ (2 * k + 1) = -(r - p) ^ (2 * k + 1) := by
    rw [pow_succ, pow_succ, heven]
    ring
  have hresponse : -reciprocalMomentTransport (2 * k) r p =
      (r - p) - (r - p) ^ (2 * k + 1) / p ^ (2 * k) := by
    rw [reciprocalMomentTransport_eq (2 * k) r p hp.ne', hodd]
    ring
  rw [hresponse]
  constructor <;> nlinarith only [he.1, he.2]

end Real
