/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring.Basic

/-!
# Centered finite product kernels

Expand a bilinear product kernel into coordinate features indexed by subsets.
The subset specialization retains every mixed term and groups it into squared
coefficients with an explicit local covariance product. Arbitrary signed
weights are allowed over a commutative ring.
-/

set_option autoImplicit false
set_option Elab.async false

universe u v w z

namespace Finset

variable {I : Type u} {A : Type v} {B : Type w} {R : Type z}
variable [DecidableEq I]

/-- Expand a product kernel into its finite coordinate features. -/
theorem sum_mul_prod_add_mul_eq_powerset [CommSemiring R] (s : Finset I) (a : Finset A)
    (b : Finset B) (f : A -> R) (g : B -> R) (c : I -> R)
    (lo hi : I -> A -> R) (lo' hi' : I -> B -> R) :
    a.sum (fun x => b.sum (fun y => f x * g y *
      s.prod (fun i => c i * hi i x * hi' i y + lo i x * lo' i y))) =
    s.powerset.sum (fun t => t.prod c *
      a.sum (fun x => f x * (t.prod (fun i => hi i x) *
        (s \ t).prod (fun i => lo i x))) *
      b.sum (fun y => g y * (t.prod (fun i => hi' i y) *
        (s \ t).prod (fun i => lo' i y)))) := by
  classical
  calc
    _ = a.sum (fun x => b.sum (fun y => s.powerset.sum (fun t =>
        f x * g y * (t.prod (fun i => c i * hi i x * hi' i y) *
          (s \ t).prod (fun i => lo i x * lo' i y))))) := by
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      rw [prod_add, mul_sum]
    _ = s.powerset.sum (fun t => a.sum (fun x => b.sum (fun y =>
        f x * g y * (t.prod (fun i => c i * hi i x * hi' i y) *
          (s \ t).prod (fun i => lo i x * lo' i y))))) := sum_comm_cycle
    _ = _ := by
      apply sum_congr rfl
      intro t ht
      calc
        _ = t.prod c *
            (a.sum (fun x => f x * (t.prod (fun i => hi i x) *
              (s \ t).prod (fun i => lo i x))) *
             b.sum (fun y => g y * (t.prod (fun i => hi' i y) *
              (s \ t).prod (fun i => lo' i y)))) := by
          rw [sum_mul_sum, mul_sum]
          apply sum_congr rfl
          intro x hx
          rw [mul_sum]
          apply sum_congr rfl
          intro y hy
          simp only [prod_mul_distrib]
          ring1
        _ = _ := (mul_assoc _ _ _).symm

/-- Coefficients after expanding each subset monomial about the local means. -/
def centeredSubsetCoefficient [CommSemiring R] (s : Finset I)
    (f : Finset I -> R) (m : I -> R) (t : Finset I) : R :=
  s.powerset.sum (fun x => f x *
    (t.prod (fun i => if Membership.mem x i then 1 else 0) *
      (s \ t).prod (fun i => if Membership.mem x i then m i else 1)))

/-- Exact centered expansion of a joint subset kernel, with all cross terms. -/
theorem sum_subset_kernel_eq_centered [CommRing R] (s : Finset I)
    (f : Finset I -> R) (m e : I -> R) :
    s.powerset.sum (fun x => s.powerset.sum (fun y => f x * f y *
      s.prod (fun i => if Membership.mem x i then
        (if Membership.mem y i then m i * e i else m i)
        else (if Membership.mem y i then m i else 1)))) =
    s.powerset.sum (fun t => t.prod (fun i => m i * (e i - m i)) *
      centeredSubsetCoefficient s f m t ^ 2) := by
  classical
  let lo : I -> Finset I -> R := fun i x => if Membership.mem x i then m i else 1
  let hi : I -> Finset I -> R := fun i x => if Membership.mem x i then 1 else 0
  let cov : I -> R := fun i => m i * (e i - m i)
  have hkernel (x y : Finset I) :
      s.prod (fun i => cov i * hi i x * hi i y + lo i x * lo i y) =
      s.prod (fun i => if Membership.mem x i then
        (if Membership.mem y i then m i * e i else m i)
        else (if Membership.mem y i then m i else 1)) := by
    apply prod_congr rfl
    intro i hiS
    by_cases hix : Membership.mem x i <;> by_cases hiy : Membership.mem y i
    all_goals simp [lo, hi, cov, hix, hiy] <;> ring1
  have hexp := sum_mul_prod_add_mul_eq_powerset s s.powerset s.powerset
    f f cov lo hi lo hi
  simp_rw [hkernel] at hexp
  simpa only [centeredSubsetCoefficient, cov, lo, hi, pow_two, mul_assoc] using hexp

end Finset
