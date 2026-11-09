/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimeSquareTail

/-! # Uniform counts for congruence-separated prime fibres

Each nonempty fibre lies in the reduced residue class of one of its members.
The existing prime-residue estimate therefore supplies one constant before
all moduli, endpoints, label types and maps. No global inverse is required.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.QRH

theorem exists_prime_fibre_count_upper :
    exists C : Real, 0 < C /\
      forall {J : Type*} [DecidableEq J] {N : Nat} [NeZero N] (X : Nat)
        (T : Finset Nat) (g : Nat -> J),
        (forall {p}, Membership.mem T p ->
          Membership.mem (Nat.primesBelow (X + 1)) p) ->
        (forall p, Membership.mem T p -> IsUnit (p : ZMod N)) ->
        (forall p, Membership.mem T p -> forall q, Membership.mem T q ->
          g p = g q -> (p : ZMod N) = (q : ZMod N)) ->
        forall u : J,
          (((T.filter (fun p => g p = u)).card : Nat) : Real) <=
            ((Nat.primesBelow (X + 1)).card : Real) / (N.totient : Real) +
              C * (X : Real) ^ (7 / 8 : Real) *
                (1 + Real.log N + Real.log ((X : Real) + 2)) ^ 2 := by
  classical
  choose C hC hBound using exists_prime_reduced_residue_count_upper
  refine Exists.intro C (And.intro hC ?_)
  intro J instJ N instN X T g hT hUnit hSep u
  let F := T.filter (fun p => g p = u)
  change (F.card : Real) <= _
  by_cases hF : F.Nonempty
  case pos =>
    choose p hp using hF
    have hpT := (Finset.mem_filter.mp hp).1
    have hpG := (Finset.mem_filter.mp hp).2
    have h := @hBound N instN (p : ZMod N) (hUnit p hpT) X
    have hSub : forall {q}, Membership.mem F q ->
        Membership.mem ((Nat.primesBelow (X + 1)).filter
          (fun q : Nat => (q : ZMod N) = (p : ZMod N))) q := by
      intro q hq
      have hqT := (Finset.mem_filter.mp hq).1
      have hqG := (Finset.mem_filter.mp hq).2
      exact Finset.mem_filter.mpr
        (And.intro (hT hqT) (hSep q hqT p hpT (hqG.trans hpG.symm)))
    have hCard : (F.card : Real) <=
        (((Nat.primesBelow (X + 1)).filter
          (fun q : Nat => (q : ZMod N) = (p : ZMod N))).card : Real) := by
      exact_mod_cast Finset.card_le_card @hSub
    exact hCard.trans h
  case neg =>
    have hZero : F.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hF)
    rw [hZero, Nat.cast_zero]
    exact add_nonneg
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity)

end PrimeFactorOscillations.QRH
