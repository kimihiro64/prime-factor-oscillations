/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimePairGreedy

/-!
# Computable complete prime-vertex selection

An accepted vertex retains every positive pair with every earlier vertex.
The test uses both square rows of all distinct pair labels.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

/-- Every distinct positive pair formed from the vertices separates in both
square rows. The vertex set is finite, so this is a computable test. -/
def nativePrimeVertexSquareFlat (P : Finset Nat) : Prop :=
  forall p : Nat, Membership.mem P p ->
  forall q : Nat, Membership.mem P q -> p < q ->
  forall r : Nat, Membership.mem P r ->
  forall s : Nat, Membership.mem P s -> r < s ->
    Not (And (p = r) (q = s)) ->
      nativePrimePairSquareCompatible (p, q - p) (r, s - r)

instance nativePrimeVertexSquareFlatDecidable (P : Finset Nat) :
    Decidable (nativePrimeVertexSquareFlat P) := by
  unfold nativePrimeVertexSquareFlat
  set_option synthInstance.maxSize 4096 in infer_instance

/-- Accept a prime exactly when its complete vertex-pair family passes the
finite square-row test. Previously accepted vertices are never removed. -/
def nativePrimeVertexGreedyInsert (P : Finset Nat) (q : Nat) : Finset Nat :=
  if Nat.Prime q /\ nativePrimeVertexSquareFlat (insert q P) then insert q P else P

/-- Visit each natural input once, accepting only admissible prime vertices. -/
def nativePrimeVertexGreedyPrefix : Nat -> Finset Nat
  | 0 => {}
  | Y + 1 => nativePrimeVertexGreedyInsert (nativePrimeVertexGreedyPrefix Y) (Y + 1)

/-- Decide global vertex membership at its birth height. -/
def nativePrimeVertexGreedyClass : Set Nat :=
  fun p => Membership.mem (nativePrimeVertexGreedyPrefix p) p

instance nativePrimeVertexGreedyClassDecidable : DecidablePred nativePrimeVertexGreedyClass :=
  fun p => inferInstanceAs (Decidable (Membership.mem (nativePrimeVertexGreedyPrefix p) p))

end PrimeFactorOscillations.FiniteFieldIntegerSignature
