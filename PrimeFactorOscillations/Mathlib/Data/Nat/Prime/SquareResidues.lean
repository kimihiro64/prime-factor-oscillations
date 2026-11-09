/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic

/-! # Products of distinct prime-square residue coordinates

Local congruences separate residues modulo the complete product. A prime
outside the coordinate set is a unit there, and the product's totient is
the product of the exact local cardinalities. These discharge the arithmetic
hypotheses of the uniform prime-fibre sampling estimate.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace Nat

theorem coprime_prime_sq_prod (S : Finset Nat) {r : Nat}
    (hr : Nat.Prime r) (hrS : Not (Membership.mem S r))
    (hS : forall p, Membership.mem S p -> Nat.Prime p) :
    Nat.Coprime (r ^ 2) (S.prod (fun p => p ^ 2)) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  apply Nat.Coprime.pow 2 2
  apply (Nat.coprime_primes hr (hS p hp)).mpr
  intro h
  apply hrS
  rwa [h]

theorem cast_zmod_prime_sq_prod_eq (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p) (a b : Nat)
    (h : forall p, Membership.mem S p -> (a : ZMod (p ^ 2)) = (b : ZMod (p ^ 2))) :
    (a : ZMod (S.prod (fun p => p ^ 2))) =
      (b : ZMod (S.prod (fun p => p ^ 2))) := by
  classical
  revert hS h
  induction S using Finset.induction_on with
  | empty =>
    intro hS h
    simp only [Finset.prod_empty]
    exact Subsingleton.elim _ _
  | @insert r S hrS ih =>
    intro hS h
    have hr := hS r (Finset.mem_insert_self r S)
    have hRest : forall p, Membership.mem S p -> Nat.Prime p := by
      intro p hp
      exact hS p (Finset.mem_insert_of_mem hp)
    have hCo := coprime_prime_sq_prod S hr hrS hRest
    rw [Finset.prod_insert hrS]
    apply (ZMod.chineseRemainder hCo).injective
    rw [map_natCast, map_natCast]
    apply Prod.ext
    { change (a : ZMod (r ^ 2)) = (b : ZMod (r ^ 2))
      exact h r (Finset.mem_insert_self r S) }
    { change (a : ZMod (S.prod (fun p => p ^ 2))) =
        (b : ZMod (S.prod (fun p => p ^ 2)))
      apply ih hRest
      intro p hp
      exact h p (Finset.mem_insert_of_mem hp) }

theorem totient_prod_prime_sq (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p) :
    (S.prod (fun p => p ^ 2)).totient = S.prod (fun p => p * (p - 1)) := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty => intro hS; simp only [Finset.prod_empty, Nat.totient_one]
  | @insert r S hrS ih =>
    intro hS
    have hr := hS r (Finset.mem_insert_self r S)
    have hRest : forall p, Membership.mem S p -> Nat.Prime p := by
      intro p hp
      exact hS p (Finset.mem_insert_of_mem hp)
    have hCo := coprime_prime_sq_prod S hr hrS hRest
    have hPhi : (r ^ 2).totient = r * (r - 1) := by
      simpa using (Nat.totient_prime_pow hr (show 0 < 2 from by decide))
    rw [Finset.prod_insert hrS, Finset.prod_insert hrS,
      Nat.totient_mul hCo, hPhi, ih hRest]

theorem isUnit_cast_prod_prime_sq (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p)
    {q : Nat} (hq : Nat.Prime q) (hqS : Not (Membership.mem S q)) :
    IsUnit (q : ZMod (S.prod (fun p => p ^ 2))) := by
  apply (ZMod.isUnit_iff_coprime q _).mpr
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  apply Nat.Coprime.pow_right 2
  apply (Nat.coprime_primes hq (hS p hp)).mpr
  intro h
  apply hqS
  rwa [h]

theorem card_prime_sq_unit_tuples (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p) :
    Nat.card ((p : S) -> Units (ZMod (p.val ^ 2))) =
      (S.prod (fun p => p ^ 2)).totient := by
  classical
  let (p : S) : NeZero (p.val ^ 2) :=
    NeZero.mk (pow_ne_zero 2 (hS p.val p.property).ne_zero)
  rw [Nat.card_eq_fintype_card, Fintype.card_pi, totient_prod_prime_sq S hS]
  simp only [ZMod.card_units_eq_totient]
  change S.attach.prod (fun p => (p.val ^ 2).totient) = _
  have hAttach : S.attach.prod (fun p => (p.val ^ 2).totient) =
      S.prod (fun p => (p ^ 2).totient) :=
    Finset.prod_attach S (fun p => (p ^ 2).totient)
  rw [hAttach]
  apply Finset.prod_congr rfl
  intro p hp
  simpa using (Nat.totient_prime_pow (hS p hp) (show 0 < 2 from by decide))

end Nat
