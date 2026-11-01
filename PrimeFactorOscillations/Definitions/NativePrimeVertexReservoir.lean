/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeVertexGreedy

/-! # Computable prime-vertex selection inside a prescribed reservoir

The supplied decision procedure is used at every birth height. No density
hypothesis or noncomputable choice enters these definitions.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

/-- Scan the reservoir, retaining the complete square-row test. -/
def nativePrimeVertexReservoirPrefix (R : Nat -> Prop) [DecidablePred R] :
    Nat -> Finset Nat
  | 0 => {}
  | Y + 1 =>
      if R (Y + 1) then
        nativePrimeVertexGreedyInsert (nativePrimeVertexReservoirPrefix R Y) (Y + 1)
      else nativePrimeVertexReservoirPrefix R Y

/-- Global membership is decided by the finite birth-height computation. -/
def nativePrimeVertexReservoirClass (R : Nat -> Prop) [DecidablePred R] : Set Nat :=
  fun p => Membership.mem (nativePrimeVertexReservoirPrefix R p) p

instance nativePrimeVertexReservoirClassDecidable (R : Nat -> Prop) [DecidablePred R] :
    DecidablePred (nativePrimeVertexReservoirClass R) :=
  fun p => inferInstanceAs (Decidable (Membership.mem (nativePrimeVertexReservoirPrefix R p) p))

end PrimeFactorOscillations.FiniteFieldIntegerSignature
