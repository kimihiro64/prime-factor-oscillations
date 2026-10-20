/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite quadratic amplitude corrections

Exact signed expansions, preservation of a signal, and completion of the
square. No cancellation bound is implied by these identities.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

/-- Expand an additive change to a finite real amplitude. -/
theorem sum_sq_amplitude_sub_mul {iota : Type*} (s : Finset iota)
    (w a c : iota -> Real) (t : Real) :
    s.sum (fun i => w i * (a i - t * c i)^2) =
      s.sum (fun i => w i * (a i)^2) -
        2 * t * s.sum (fun i => w i * a i * c i) +
        t^2 * s.sum (fun i => w i * (c i)^2) := by
  calc
    _ = s.sum (fun i => w i * (a i)^2 -
        (2 * t) * (w i * a i * c i) + t^2 * (w i * (c i)^2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        <- Finset.mul_sum, <- Finset.mul_sum]

/-- A correction vanishing on a signal preserves its weighted square sum. -/
theorem sum_sq_amplitude_sub_mul_signal {iota : Type*}
    (s : Finset iota) (w a c z : iota -> Real) (t : Real)
    (hcz : forall i, Membership.mem s i -> z i * c i = 0) :
    s.sum (fun i => w i * (a i - t * c i)^2 * z i) =
      s.sum (fun i => w i * (a i)^2 * z i) := by
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = w i * (a i)^2 * z i +
        (-2 * w i * a i * t + w i * t^2 * c i) * (z i * c i) := by
      ring
    _ = _ := by rw [hcz i hi]; ring

/-- Complete the square for a general additive amplitude correction. -/
theorem sum_sq_amplitude_sub_mul_completed {iota : Type*}
    (s : Finset iota) (w a c : iota -> Real) (t : Real)
    (h2 : Not (s.sum (fun i => w i * (c i)^2) = 0)) :
    s.sum (fun i => w i * (a i - t * c i)^2) =
      s.sum (fun i => w i * (a i)^2) -
        (s.sum (fun i => w i * a i * c i))^2 /
          s.sum (fun i => w i * (c i)^2) +
      s.sum (fun i => w i * (c i)^2) *
        (t - s.sum (fun i => w i * a i * c i) /
          s.sum (fun i => w i * (c i)^2))^2 := by
  rw [sum_sq_amplitude_sub_mul]
  field_simp [h2]
  ring

/-- The optimized additive amplitude has no larger mass than any parameter. -/
theorem sum_sq_amplitude_sub_mul_min {iota : Type*}
    (s : Finset iota) (w a c : iota -> Real) (t : Real)
    (h2 : 0 < s.sum (fun i => w i * (c i)^2)) :
    s.sum (fun i => w i * (a i)^2) -
      (s.sum (fun i => w i * a i * c i))^2 /
        s.sum (fun i => w i * (c i)^2) <=
      s.sum (fun i => w i * (a i - t * c i)^2) := by
  rw [sum_sq_amplitude_sub_mul_completed s w a c t (ne_of_gt h2)]
  exact le_add_of_nonneg_right (mul_nonneg (le_of_lt h2) (sq_nonneg _))

end Finset
