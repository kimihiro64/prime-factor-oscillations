/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocalCoercivity

/-!
# Integrated upper cost and an escaping positive probe

The upper integral bound complements the probe-uniform lower bound. Its
explicit positive probe makes an arbitrarily long incoming displacement cost
strictly less than half the reference, with a quantitative positive margin.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

/-- Integrating the cubic reciprocal majorant gives the full incoming upper cost. -/
theorem incoming_integrated_normalized_pairLogDefect_upper (t r q : Real)
    (ht : 0 < t) (hr : 0 < r) (hrq : r <= q) :
    r ^ 2 * (r + t) / t ^ 2 * pairLogDefect t r q <=
      (r + t) / 2 * (1 - (r / q) ^ 2) := by
  let c := r ^ 2 * (r + t) / t ^ 2
  let a := r ^ 2 * (r + t) / 2
  let F := fun x : Real => -c * bernoulliLogProfile t x - a / x ^ 2
  let dF := fun x : Real => r ^ 2 * (r + t) * t / (x ^ 3 * (x + t))
  have hder : forall x : Real, 0 < x -> HasDerivAt F (dF x) x := by
    intro x hx
    have hd := ((hasDerivAt_bernoulliLogProfile t x ht hx).const_mul (-c)).sub
      ((hasDerivAt_const x a).div ((hasDerivAt_id x).pow 2)
        (pow_ne_zero 2 hx.ne'))
    convert hd using 1
    . dsimp [F]
      rfl
    . dsimp [c, a, dF]
      field_simp [hx.ne', ht.ne', (add_pos hx ht).ne']
      ring
  have hcont : ContinuousOn F (Set.Icc r q) := by
    intro x hx
    exact (hder x (hr.trans_le hx.1)).continuousAt.continuousWithinAt
  have hmono : MonotoneOn F (Set.Icc r q) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc r q) hcont
      (fun x hx => (hder x (hr.trans_le (interior_subset hx).1)).hasDerivWithinAt)
      (by
        intro x hx
        have hxpos := hr.trans_le (interior_subset hx).1
        dsimp [dF]
        positivity)
  have h := hmono (Set.left_mem_Icc.mpr hrq) (Set.right_mem_Icc.mpr hrq) hrq
  have hq : 0 < q := hr.trans_le hrq
  have hid : a / r ^ 2 - a / q ^ 2 =
      (r + t) / 2 * (1 - (r / q) ^ 2) := by
    dsimp [a]
    field_simp [hr.ne', hq.ne']
  change -c * bernoulliLogProfile t r - a / r ^ 2 <=
    -c * bernoulliLogProfile t q - a / q ^ 2 at h
  unfold pairLogDefect
  change c * _ <= _
  rw [<- hid]
  nlinarith only [h]

/-- A probe tuned to the incoming coordinate, with no finite upper cutoff. -/
def halfReferenceEscapeProbe (r q : Real) : Real :=
  r ^ 3 / (2 * (q ^ 2 - r ^ 2))

/-- Every coordinate strictly above the positive reference gives a positive probe. -/
theorem halfReferenceEscapeProbe_pos (r q : Real) (hr : 0 < r) (hrq : r < q) :
    0 < halfReferenceEscapeProbe r q := by
  have hgap : 0 < q ^ 2 - r ^ 2 := by nlinarith only [hr, hrq]
  unfold halfReferenceEscapeProbe
  positivity

/-- The tuned probe stays below half the reference with an explicit positive margin. -/
theorem halfReferenceEscapeProbe_cost_le (r q : Real) (hr : 0 < r) (hrq : r < q) :
    r ^ 2 * (r + halfReferenceEscapeProbe r q) /
        halfReferenceEscapeProbe r q ^ 2 *
          pairLogDefect (halfReferenceEscapeProbe r q) r q <=
      r / 2 - r ^ 3 / (4 * q ^ 2) := by
  have ht := halfReferenceEscapeProbe_pos r q hr hrq
  have h := incoming_integrated_normalized_pairLogDefect_upper
    (halfReferenceEscapeProbe r q) r q ht hr hrq.le
  have hq : 0 < q := hr.trans hrq
  have hgap : 0 < q ^ 2 - r ^ 2 := by nlinarith only [hr, hrq]
  have hid : (r + halfReferenceEscapeProbe r q) / 2 * (1 - (r / q) ^ 2) =
      r / 2 - r ^ 3 / (4 * q ^ 2) := by
    unfold halfReferenceEscapeProbe
    field_simp [hq.ne', hgap.ne']
    ring
  rwa [hid] at h

end Real
