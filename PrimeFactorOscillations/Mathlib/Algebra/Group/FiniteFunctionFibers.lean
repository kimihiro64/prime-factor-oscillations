/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Algebra.Group.FiniteSumFibers

/-!
# Exact fibers after adding a nonzero residue

For an arbitrary function on a finite domain, exactly one nonzero additive
coordinate works at each point where the function is nonzero.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace Finset

theorem card_function_add_nonzero_eq {I K : Type*} [Fintype K]
    [DecidableEq I] [DecidableEq K] [AddCommGroup K]
    (S : Finset I) (f : I -> K) :
    ((S.product (Finset.univ.erase (0 : K))).filter
      (fun ab : Prod I K => f ab.1 + ab.2 = 0)).card =
      (S.filter (fun a => Not (f a = 0))).card := by
  symm
  apply Finset.card_bij (fun a _ => (a, -f a))
  . intro a ha
    have h := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_product.mpr (And.intro h.1 ?_)) (add_neg_cancel _)
    exact Finset.mem_erase.mpr (And.intro (neg_ne_zero.mpr h.2) (Finset.mem_univ _))
  . intro a _ b _ h
    exact congrArg Prod.fst h
  . intro ab hab
    have h := Finset.mem_filter.mp hab
    have hm := Finset.mem_product.mp h.1
    have hn := (Finset.mem_erase.mp hm.2).1
    have he : -f ab.1 = ab.2 := by
      apply neg_eq_iff_add_eq_zero.mpr
      simpa only [add_comm] using h.2
    have hf : Not (f ab.1 = 0) := by
      intro hz
      apply hn
      rw [<- he, hz, neg_zero]
    refine Exists.intro ab.1 (Exists.intro (Finset.mem_filter.mpr (And.intro hm.1 hf)) ?_)
    exact Prod.ext rfl he

theorem card_function_add_nonzero {I K : Type*} [Fintype K]
    [DecidableEq I] [DecidableEq K] [AddCommGroup K]
    (S : Finset I) (f : I -> K) :
    ((S.product (Finset.univ.erase (0 : K))).filter
      (fun ab : Prod I K => f ab.1 + ab.2 = 0)).card =
      S.card - (S.filter (fun a => f a = 0)).card := by
  classical
  rw [card_function_add_nonzero_eq]
  have heq : S.filter (fun a => Not (f a = 0)) = S \ S.filter (fun a => f a = 0) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    . intro h
      exact And.intro h.1 (fun hh => h.2 hh.2)
    . intro h
      exact And.intro h.1 (fun hh => h.2 (And.intro h.1 hh))
  rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]

theorem card_function_add_two_nonzero {I K : Type*} [Fintype K]
    [DecidableEq I] [DecidableEq K] [AddCommGroup K]
    (hK : 2 <= Fintype.card K) (S : Finset I) (f : I -> K) :
    (((S.product (Finset.univ.erase (0 : K))).product
        (Finset.univ.erase (0 : K))).filter
      (fun ab : Prod (Prod I K) K => f ab.1.1 + ab.1.2 + ab.2 = 0)).card =
      S.card * (Fintype.card K - 2) + (S.filter (fun a => f a = 0)).card := by
  rw [card_function_add_nonzero (S.product (Finset.univ.erase (0 : K)))
    (fun ab : Prod I K => f ab.1 + ab.2)]
  have hProd : (S.product (Finset.univ.erase (0 : K))).card =
      S.card * (Finset.univ.erase (0 : K)).card := Finset.card_product _ _
  rw [hProd, card_function_add_nonzero S f,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : K)), Finset.card_univ]
  have hStep : Fintype.card K - 1 = (Fintype.card K - 2) + 1 := by omega
  have hCount := Finset.card_filter_le S (fun a => f a = 0)
  rw [hStep, Nat.mul_add, Nat.mul_one]
  omega

end Finset
