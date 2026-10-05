/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Ring.Basic

/-!
# Square divisibility from inert prime factors

A squarefree divisor supported on primes congruent to three modulo four
must divide both coordinates of any represented multiple. Its square
therefore divides the sum of squares. No primitivity assumption is used.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- An inert prime dividing a sum of squares divides its first coordinate. -/
theorem Prime.dvd_left_of_mod_four_eq_three_of_dvd_sq_add_sq
    {q a b : Nat} (hq : q.Prime) (hmod : q % 4 = 3)
    (hdiv : Dvd.dvd q (a ^ 2 + b ^ 2)) : Dvd.dvd q a := by
  let : Fact q.Prime := Fact.mk hq
  have hz : (a : ZMod q) ^ 2 + (b : ZMod q) ^ 2 = 0 := by
    have hcast := (ZMod.natCast_eq_zero_iff (a ^ 2 + b ^ 2) q).mpr hdiv
    simpa only [Nat.cast_add, Nat.cast_pow] using hcast
  by_contra hqa
  have hneq : Not ((a : ZMod q) = 0) := by
    intro h
    exact hqa ((ZMod.natCast_eq_zero_iff a q).mp h)
  exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq hneq
    (eq_neg_of_add_eq_zero_left hz)) hmod

/-- A squarefree product of inert primes divides both coordinates of a represented multiple. -/
theorem dvd_left_of_squarefree_of_inert_of_dvd_sq_add_sq
    {v a b : Nat} (hv : Squarefree v)
    (hinert : forall q : Nat, q.Prime -> Dvd.dvd q v -> q % 4 = 3)
    (hdiv : Dvd.dvd v (a ^ 2 + b ^ 2)) : Dvd.dvd v a := by
  by_cases ha : a = 0
  next => simpa only [ha] using (dvd_zero v)
  next =>
    rw [<- Nat.prod_primeFactors_of_squarefree hv]
    apply (Nat.prod_primeFactors_dvd_iff ha).mpr
    intro q hq
    have hp := Nat.prime_of_mem_primeFactors hq
    have hqv := Nat.dvd_of_mem_primeFactors hq
    have hqa := hp.dvd_left_of_mod_four_eq_three_of_dvd_sq_add_sq
      (hinert q hp hqv) (hqv.trans hdiv)
    exact Nat.mem_primeFactors.mpr (And.intro hp (And.intro hqa ha))

/-- An inert squarefree divisor of a sum of two squares divides it squared. -/
theorem sq_dvd_of_squarefree_of_inert_of_dvd_sq_add_sq
    {v a b : Nat} (hv : Squarefree v)
    (hinert : forall q : Nat, q.Prime -> Dvd.dvd q v -> q % 4 = 3)
    (hdiv : Dvd.dvd v (a ^ 2 + b ^ 2)) :
    Dvd.dvd (v ^ 2) (a ^ 2 + b ^ 2) := by
  have ha := dvd_left_of_squarefree_of_inert_of_dvd_sq_add_sq hv hinert hdiv
  have hb := dvd_left_of_squarefree_of_inert_of_dvd_sq_add_sq hv hinert
    (show Dvd.dvd v (b ^ 2 + a ^ 2) by simpa only [Nat.add_comm] using hdiv)
  cases ha with
  | intro u hu =>
    cases hb with
    | intro w hw =>
      refine Exists.intro (u ^ 2 + w ^ 2) ?_
      rw [hu, hw]
      ring

end Nat
