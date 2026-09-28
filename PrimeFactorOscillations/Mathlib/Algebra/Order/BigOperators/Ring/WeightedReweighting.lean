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
# Finite quadratic reweighting

An auxiliary statistic that vanishes on the signal can change a nonnegative
weight without changing its signal-weighted sum. The complete-square identity
retains the cost of that change and identifies the exact second-moment optimum.
-/

namespace Finset

/-- Expand the total mass after quadratic reweighting. -/
theorem sum_sq_reweight {iota : Type*} (s : Finset iota)
    (w y : iota -> Real) (t : Real) :
    s.sum (fun i => w i * (1 - t * y i)^2) =
      s.sum w - 2 * t * s.sum (fun i => w i * y i) +
        t^2 * s.sum (fun i => w i * (y i)^2) := by
  calc
    _ = s.sum (fun i => w i - (2 * t) * (w i * y i) +
        t^2 * (w i * (y i)^2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        <- Finset.mul_sum, <- Finset.mul_sum]

/-- A statistic vanishing on the signal preserves the signal-weighted sum. -/
theorem sum_sq_reweight_mul_eq_of_mul_eq_zero {iota : Type*}
    (s : Finset iota) (w y z : iota -> Real) (t : Real)
    (hyz : forall i, Membership.mem s i -> z i * y i = 0) :
    s.sum (fun i => w i * (1 - t * y i)^2 * z i) =
      s.sum (fun i => w i * z i) := by
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = w i * z i + (-2 * w i * t + w i * t^2 * y i) * (z i * y i) := by
      ring
    _ = _ := by rw [hyz i hi]; ring

/-- Complete the square using the first and nonzero second weighted moments. -/
theorem sum_sq_reweight_eq_completed_square {iota : Type*}
    (s : Finset iota) (w y : iota -> Real) (t : Real)
    (h2 : Not (s.sum (fun i => w i * (y i)^2) = 0)) :
    s.sum (fun i => w i * (1 - t * y i)^2) =
      s.sum w - (s.sum (fun i => w i * y i))^2 /
        s.sum (fun i => w i * (y i)^2) +
      s.sum (fun i => w i * (y i)^2) *
        (t - s.sum (fun i => w i * y i) /
          s.sum (fun i => w i * (y i)^2))^2 := by
  rw [sum_sq_reweight]
  field_simp [h2]
  ring

/-- The completed-square value bounds the mass for every reweighting parameter. -/
theorem sum_sq_reweight_min {iota : Type*}
    (s : Finset iota) (w y : iota -> Real) (t : Real)
    (h2 : 0 < s.sum (fun i => w i * (y i)^2)) :
    s.sum w - (s.sum (fun i => w i * y i))^2 /
      s.sum (fun i => w i * (y i)^2) <=
        s.sum (fun i => w i * (1 - t * y i)^2) := by
  rw [sum_sq_reweight_eq_completed_square s w y t (ne_of_gt h2)]
  exact le_add_of_nonneg_right (mul_nonneg (le_of_lt h2) (sq_nonneg _))

end Finset
