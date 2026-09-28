/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card

/-! # Counting nonzero additive pairs with a specified sum -/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

/-- Nonzero pairs with sum t correspond to all a except zero and t. -/
theorem card_nonzero_sum_fiber {A : Type*} [AddCommGroup A] [Fintype A]
    [DecidableEq A] (t : A) :
    (((univ.erase (0 : A)).product (univ.erase (0 : A))).filter
      (fun ab : Prod A A => ab.1 + ab.2 = t)).card =
      ((univ.erase (0 : A)).erase t).card := by
  symm
  apply Finset.card_bij (fun a _ => (a, t - a))
  next =>
    intro a ha
    have hat : Not (a = t) := (Finset.mem_erase.mp ha).1
    have ha0 : Not (a = 0) := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    apply Finset.mem_filter.mpr
    constructor
    next =>
      apply Finset.mem_product.mpr
      constructor
      next => exact Finset.mem_erase.mpr (And.intro ha0 (Finset.mem_univ a))
      next =>
        apply Finset.mem_erase.mpr
        refine And.intro ?_ (Finset.mem_univ _)
        intro hz
        have heq : t = a := sub_eq_zero.mp hz
        exact hat heq.symm
    next => rw [add_comm a (t - a), sub_add_cancel]
  next =>
    intro a _ b _ hab
    exact congrArg Prod.fst hab
  next =>
    intro ab hab
    have hmem := Finset.mem_filter.mp hab
    have hpair := Finset.mem_product.mp hmem.1
    have ha0 := (Finset.mem_erase.mp hpair.1).1
    have hb0 := (Finset.mem_erase.mp hpair.2).1
    have hasum := hmem.2
    have hat : Not (ab.1 = t) := by
      intro heq
      have hz : ab.2 = 0 := by
        apply add_left_cancel (a := ab.1)
        simpa only [add_zero, heq] using hasum
      exact hb0 hz
    refine Exists.intro ab.1 (Exists.intro ?_ ?_)
    next =>
      exact Finset.mem_erase.mpr (And.intro hat
        (Finset.mem_erase.mpr (And.intro ha0 (Finset.mem_univ _))))
    next =>
      apply Prod.ext
      next => rfl
      next =>
        change t - ab.1 = ab.2
        apply sub_eq_iff_eq_add.mpr
        simpa only [add_comm] using hasum.symm

/-- The exceptional zero sum has one additional nonzero-pair solution. -/
theorem card_nonzero_sum_fiber_explicit {A : Type*} [AddCommGroup A] [Fintype A]
    [DecidableEq A] (hcard : 2 <= Fintype.card A) (t : A) :
    (((univ.erase (0 : A)).product (univ.erase (0 : A))).filter
      (fun ab : Prod A A => ab.1 + ab.2 = t)).card =
      Fintype.card A - 2 + if t = 0 then 1 else 0 := by
  rw [card_nonzero_sum_fiber]
  by_cases ht : t = 0
  next =>
    subst t
    rw [Finset.erase_idem, Finset.card_erase_of_mem (Finset.mem_univ (0 : A))]
    rw [Finset.card_univ, ite_eq_left (show (0 : A) = 0 from rfl)]
    omega
  next =>
    have hm : Membership.mem (univ.erase (0 : A)) t :=
      Finset.mem_erase.mpr (And.intro ht (Finset.mem_univ t))
    rw [Finset.card_erase_of_mem hm,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : A))]
    rw [ite_eq_right ht]
    change Fintype.card A - 1 - 1 = Fintype.card A - 2 + 0
    omega

/-- Exact nonzero-pair count for any set of allowed additive roots.
Distinct roots are counted once, including all collisions automatically. -/
theorem card_nonzero_sum_mem {A : Type*} [AddCommGroup A] [Fintype A]
    [DecidableEq A] (hcard : 2 <= Fintype.card A) (R : Finset A) :
    (((univ.erase (0 : A)).product (univ.erase (0 : A))).filter
      (fun ab : Prod A A => Membership.mem R (ab.1 + ab.2))).card =
      R.card * (Fintype.card A - 2) + if Membership.mem R 0 then 1 else 0 := by
  rw [<- Finset.sum_card_fiberwise_eq_card_filter
    ((univ.erase (0 : A)).product (univ.erase (0 : A))) R
    (fun ab : Prod A A => ab.1 + ab.2)]
  simp_rw [card_nonzero_sum_fiber_explicit hcard]
  simp [Finset.sum_add_distrib]

end Finset
