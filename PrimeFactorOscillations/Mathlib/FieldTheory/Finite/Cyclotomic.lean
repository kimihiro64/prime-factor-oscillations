/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Cyclotomic root counts over finite fields

The roots of a cyclotomic polynomial of index nonzero in a finite field
number either Euler's totient or zero, according as the index divides the
cardinality of the multiplicative group. This is the local counting input
for cyclotomic polynomial divisibility laws.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Primitive roots in a finite field have the full totient count exactly
when their order divides the cardinality of the multiplicative group. -/
theorem card_primitiveRoots_of_finite (n : Nat) (hn : 0 < n) :
    (primitiveRoots n K).card =
      if Dvd.dvd n (Fintype.card K - 1) then Nat.totient n else 0 := by
  classical
  by_cases hd : Dvd.dvd n (Fintype.card K - 1)
  { rw [ite_eq_left hd]
    have hdu : Dvd.dvd n (Fintype.card (Units K)) := by
      simpa only [Fintype.card_units] using hd
    have hc := @IsCyclic.card_orderOf_eq_totient (Units K) _ _ _ n hdu
    have hpos :
        0 < (Finset.univ.filter (fun u : Units K => orderOf u = n)).card := by
      rw [hc]
      exact Nat.totient_pos.mpr hn
    choose u hu using Finset.card_pos.mp hpos
    have ho : orderOf u = n := (Finset.mem_filter.mp hu).2
    have hr : IsPrimitiveRoot (u : K) n :=
      IsPrimitiveRoot.iff_orderOf.mpr (orderOf_units.trans ho)
    exact hr.card_primitiveRoots }
  { rw [ite_eq_right hd]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hr := isPrimitiveRoot_of_mem_primitiveRoots hx
    let u : Units K := (hr.isUnit (Nat.ne_of_gt hn)).unit
    have hu : (u : K) = x := (hr.isUnit (Nat.ne_of_gt hn)).unit_spec
    have ho : orderOf u = n := by
      rw [<- orderOf_units, hu]
      exact IsPrimitiveRoot.iff_orderOf.mp hr
    apply hd
    rw [<- ho, <- Fintype.card_units K]
    exact orderOf_dvd_card }

/-- The complete root multiset has either totient cardinality or is empty;
the nonzero characteristic hypothesis excludes ramified indices. -/
theorem card_cyclotomic_roots (n : Nat) [NeZero (n : K)] :
    (Polynomial.cyclotomic n K).roots.card =
      if Dvd.dvd n (Fintype.card K - 1) then Nat.totient n else 0 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by
    apply NeZero.ne (n : K)
    rw [h]
    exact Nat.cast_zero)
  rw [Polynomial.cyclotomic.roots_eq_primitiveRoots_val]
  exact card_primitiveRoots_of_finite n hn

/-- Counting the roots as field elements gives the same explicit local law. -/
theorem card_cyclotomic_root_filter (n : Nat) [NeZero (n : K)] :
    (Finset.univ.filter
      (fun x : K => (Polynomial.cyclotomic n K).IsRoot x)).card =
      if Dvd.dvd n (Fintype.card K - 1) then Nat.totient n else 0 := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by
    apply NeZero.ne (n : K)
    rw [h]
    exact Nat.cast_zero)
  have heq :
      Finset.univ.filter (fun x : K => (Polynomial.cyclotomic n K).IsRoot x) =
        primitiveRoots n K := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_primitiveRoots hn]
    exact Polynomial.isRoot_cyclotomic_iff
  rw [heq]
  exact card_primitiveRoots_of_finite n hn

end FiniteField
