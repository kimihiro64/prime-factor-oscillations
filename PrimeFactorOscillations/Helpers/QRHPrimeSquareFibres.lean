/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimeFibreOccupancy
import PrimeFactorOscillations.Mathlib.Data.Nat.Prime.SquareResidues

/-! # Uniform occupancy of actual prime-square residue tuples

All regular primes and every tuple label are included. The single constant
precedes the coordinate prime set, endpoint and label; primes belonging to
the coordinate support are exactly the omitted finite exceptional set.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.QRH

theorem exists_prime_square_tuple_fibre_count_upper :
    exists C : Real, 0 < C /\
      forall (S : Finset Nat),
        (forall p, Membership.mem S p -> Nat.Prime p) ->
        forall (X : Nat) (u : (p : S) -> ZMod (p.val ^ 2)),
          ((((Nat.primesBelow (X + 1)).filter (fun q => Not (Membership.mem S q))).filter
            (fun q => (fun p : S => (q : ZMod (p.val ^ 2))) = u)).card : Real) <=
            ((Nat.primesBelow (X + 1)).card : Real) /
              ((S.prod (fun p => p * (p - 1)) : Nat) : Real) +
            C * (X : Real) ^ (7 / 8 : Real) *
              (1 + Real.log ((S.prod (fun p => p ^ 2) : Nat) : Real) +
                Real.log ((X : Real) + 2)) ^ 2 := by
  classical
  choose C hC hBound using exists_prime_fibre_count_upper
  refine Exists.intro C (And.intro hC ?_)
  intro S hS X u
  let N := S.prod (fun p => p ^ 2)
  have hN : Not (N = 0) := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero 2 (hS p hp).ne_zero
  let instN : NeZero N := NeZero.mk hN
  let T := (Nat.primesBelow (X + 1)).filter (fun q => Not (Membership.mem S q))
  let g (q : Nat) : (p : S) -> ZMod (p.val ^ 2) := fun p => (q : ZMod (p.val ^ 2))
  have hT : forall {q}, Membership.mem T q ->
      Membership.mem (Nat.primesBelow (X + 1)) q := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hUnit : forall q, Membership.mem T q -> IsUnit (q : ZMod N) := by
    intro q hq
    have hqPrime := (Nat.mem_primesBelow.mp (hT hq)).2
    exact Nat.isUnit_cast_prod_prime_sq S hS hqPrime (Finset.mem_filter.mp hq).2
  have hSep : forall a, Membership.mem T a -> forall b, Membership.mem T b ->
      g a = g b -> (a : ZMod N) = (b : ZMod N) := by
    intro a ha b hb hab
    apply Nat.cast_zmod_prime_sq_prod_eq S hS
    intro p hp
    exact congrArg (fun v : (p : S) -> ZMod (p.val ^ 2) =>
      v (Subtype.mk p hp)) hab
  have h := @hBound ((p : S) -> ZMod (p.val ^ 2)) (Classical.decEq _) N instN X T g
    hT hUnit hSep u
  have hPhi : N.totient = S.prod (fun p => p * (p - 1)) :=
    Nat.totient_prod_prime_sq S hS
  rw [hPhi] at h
  simpa only [N, T, g] using h

end PrimeFactorOscillations.QRH
