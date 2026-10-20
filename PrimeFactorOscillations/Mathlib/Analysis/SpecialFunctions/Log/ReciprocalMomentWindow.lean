/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.ReciprocalMomentTransport

/-!
# Reciprocal-moment transport on a fixed relative window

Use the actual displacement divided by its coordinate, rather than a
coarser budget divided by the reference. The entering window p<=2r
and leaving window 2r<=3p both give a uniform ratio at most one half.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

/-- Normalize only the auxiliary scale in the existing all-order remainder. -/
theorem reciprocal_moment_remainder_le_ratio (m : Nat) (p x rho : Real)
    (hp : 0 < p) (hx : 0 <= x) (hrho : 0 <= rho) (hrelative : x <= rho * p) :
    0 <= x ^ (m + 1) / p ^ m /\
      x ^ (m + 1) / p ^ m <= rho ^ m * x := by
  have hb := reciprocal_moment_remainder_le m 1 (rho / 4) p x
    (by norm_num) (by positivity) hp hx (by nlinarith only [hrelative])
  have hid : 4 * (rho / 4) / (1 : Real) = rho := by ring
  rw [hid] at hb
  exact hb

/-- The entire entering window has geometric ratio at most one half. -/
theorem reciprocalMomentTransport_entering_half_window_bounds
    (m : Nat) (r p : Real) (hr : 0 < r) (hrp : r <= p) (hwindow : p <= 2 * r) :
    (1 - (1 / 2 : Real) ^ m) * (p - r) <= reciprocalMomentTransport m r p /\
      reciprocalMomentTransport m r p <= p - r := by
  have hp : 0 < p := hr.trans_le hrp
  have hb := reciprocal_moment_remainder_le_ratio m p (p - r) (1 / 2)
    hp (sub_nonneg.mpr hrp) (by norm_num) (by linarith only [hwindow])
  rw [reciprocalMomentTransport_eq m r p hp.ne']
  constructor <;> nlinarith only [hb.1, hb.2]

/-- At even order the matching leaving response has the same half ratio. -/
theorem reciprocalMomentTransport_leaving_half_window_bounds
    (k : Nat) (r p : Real) (hp : 0 < p) (hpr : p <= r) (hwindow : 2 * r <= 3 * p) :
    (1 - (1 / 2 : Real) ^ (2 * k)) * (r - p) <=
        -reciprocalMomentTransport (2 * k) r p /\
      -reciprocalMomentTransport (2 * k) r p <= r - p := by
  have hb := reciprocal_moment_remainder_le_ratio (2 * k) p (r - p) (1 / 2)
    hp (sub_nonneg.mpr hpr) (by norm_num) (by linarith only [hwindow])
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
  constructor <;> nlinarith only [hb.1, hb.2]

end Real
