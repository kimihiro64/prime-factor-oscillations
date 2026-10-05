/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Signed quadratic minima

For positive finite weights, the quadratic form with reciprocal weights has
minimum the reciprocal of their sum under a signed unit-mass constraint.
The explicit minimizing vector is normalized here. This is the finite
optimization step used after a sieve quadratic form has been diagonalized.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

variable {I : Type*}

/-- Weighted Cauchy-Schwarz under a signed unit-mass constraint. -/
theorem sum_sq_div_ge_of_signed_sum_eq_one (s : Finset I)
    (f e y : I -> Real) (hf : forall i, Membership.mem s i -> 0 < f i)
    (he : forall i, Membership.mem s i -> e i ^ 2 = 1)
    (hy : s.sum (fun i => e i * y i) = 1) :
    1 / s.sum f <= s.sum (fun i => y i ^ 2 / f i) := by
  calc
    _ = (s.sum (fun i => e i * y i)) ^ 2 / s.sum f := by rw [hy]; simp
    _ <= s.sum (fun i => (e i * y i) ^ 2 / f i) :=
      sq_sum_div_le_sum_sq_div s (fun i => e i * y i) hf
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      rw [mul_pow, he i hi, one_mul]

/-- The proposed minimizing vector has signed mass one. -/
theorem sum_signed_normalized_eq_one (s : Finset I) (f e : I -> Real)
    (he : forall i, Membership.mem s i -> e i ^ 2 = 1) (hH : Not (s.sum f = 0)) :
    s.sum (fun i => e i * (e i * f i / s.sum f)) = 1 := by
  calc
    _ = s.sum (fun i => f i / s.sum f) := by
      apply sum_congr rfl
      intro i hi
      rw [<- mul_div_assoc, <- mul_assoc, <- pow_two, he i hi, one_mul]
    _ = s.sum f / s.sum f := by simp only [div_eq_mul_inv, sum_mul]
    _ = 1 := div_self hH

/-- The proposed minimizing vector attains the reciprocal total weight. -/
theorem sum_sq_div_signed_normalized_eq_inv (s : Finset I) (f e : I -> Real)
    (hf : forall i, Membership.mem s i -> Not (f i = 0))
    (he : forall i, Membership.mem s i -> e i ^ 2 = 1) (hH : Not (s.sum f = 0)) :
    s.sum (fun i => (e i * f i / s.sum f) ^ 2 / f i) = 1 / s.sum f := by
  calc
    _ = s.sum (fun i => f i / (s.sum f) ^ 2) := by
      apply sum_congr rfl
      intro i hi
      rw [div_pow, mul_pow, he i hi, one_mul]
      field_simp [hf i hi, hH]
    _ = s.sum f / (s.sum f) ^ 2 := by simp only [div_eq_mul_inv, sum_mul]
    _ = 1 / s.sum f := by field_simp [hH]

end Finset
