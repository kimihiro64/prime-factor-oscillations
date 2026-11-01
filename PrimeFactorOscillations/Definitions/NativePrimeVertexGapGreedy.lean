/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeVertexGapIndependent

/-! # Computable complete vertex/gap squareclass selection

Every membership decision is a finite scan using the full independence test.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativePrimeVertexGapGreedyInsert (P : Finset Nat) (q : Nat) : Finset Nat :=
  if And (Nat.Prime q) (nativePrimeVertexGapIndependent (insert q P)) then
    insert q P else P

def nativePrimeVertexGapReservoirPrefix (R : Nat -> Prop) [DecidablePred R] :
    Nat -> Finset Nat
  | 0 => {}
  | Y + 1 =>
      if R (Y + 1) then
        nativePrimeVertexGapGreedyInsert (nativePrimeVertexGapReservoirPrefix R Y) (Y + 1)
      else nativePrimeVertexGapReservoirPrefix R Y

def nativePrimeVertexGapReservoirClass (R : Nat -> Prop) [DecidablePred R] : Set Nat :=
  fun p => Membership.mem (nativePrimeVertexGapReservoirPrefix R p) p

instance nativePrimeVertexGapReservoirClassDecidable (R : Nat -> Prop) [DecidablePred R] :
    DecidablePred (nativePrimeVertexGapReservoirClass R) :=
  fun p => inferInstanceAs
    (Decidable (Membership.mem (nativePrimeVertexGapReservoirPrefix R p) p))

end PrimeFactorOscillations.FiniteFieldIntegerSignature
