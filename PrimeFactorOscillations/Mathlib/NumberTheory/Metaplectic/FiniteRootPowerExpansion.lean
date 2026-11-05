/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# One integral counting profile for all positive power probes

A finite family taking values among zero and n prescribed powers has a
single natural coefficient vector representing every positive power sum.
Its total mass is exactly the number of nonzero family values. This supplies
the simultaneous coefficient orbit required by the septic nonvanishing input;
it does not estimate the corresponding character sum.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace FiniteRootPower

theorem exists_counting_profile {R : Type*} [CommSemiring R] [DecidableEq R]
    {I : Type*} (n : Nat) (f : I -> R) (z : R)
    (hf : forall x : I, f x = 0 \/
      Exists fun j : Fin n => f x = z ^ j.val)
    (S : Finset I) :
    Exists fun v : Fin n -> Nat =>
      (Finset.univ.sum v = (S.filter fun x => Not (f x = 0)).card) /\
      (forall r : Nat, 0 < r ->
        S.sum (fun x => f x ^ r) =
          Finset.univ.sum (fun j => (v j : R) * (z ^ j.val) ^ r)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    apply Exists.intro (fun _ => 0)
    constructor
    . simp
    . intro r hr
      simp
  | @insert x S hx ih =>
    cases ih with
    | intro v hv =>
      by_cases hfx : f x = 0
      . apply Exists.intro v
        constructor
        . simpa [Finset.filter_insert, hfx] using hv.1
        . intro r hr
          rw [Finset.sum_insert hx, hfx, zero_pow (Nat.ne_of_gt hr), zero_add]
          exact hv.2 r hr
      . cases Or.resolve_left (hf x) hfx with
        | intro j hj =>
          let w : Fin n -> Nat := fun i => v i + if i = j then 1 else 0
          apply Exists.intro w
          constructor
          . have hnot : Not (Membership.mem
                (S.filter fun t => Not (f t = 0)) x) := by
              intro hmem
              exact hx (Finset.mem_filter.mp hmem).1
            simp [w, Finset.sum_add_distrib, Finset.filter_insert,
              hfx, hnot, hv.1, add_comm]
          . intro r hr
            rw [Finset.sum_insert hx, hj, hv.2 r hr]
            simp [w, add_mul, Finset.sum_add_distrib, add_comm]

end FiniteRootPower
