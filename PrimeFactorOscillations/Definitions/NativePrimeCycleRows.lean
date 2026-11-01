/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeVertexGapIndependent

/-! # Native row incidence multiplicities and even-degree edge sets -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativePrimeVertexEdges (P : Finset Nat) : Finset (Prod Nat Nat) :=
  (P.product P).filter (fun e => e.1 < e.2)

def nativeVertexGapRowMultiplicity (A B : Finset (Prod Nat Nat))
    (x : Sum Nat (Prod Nat Nat)) : Nat :=
  ((A.filter (fun e => (Sum.inl e.1 : Sum Nat (Prod Nat Nat)) = x)).card +
    (A.filter (fun e => (Sum.inr e : Sum Nat (Prod Nat Nat)) = x)).card) +
  ((B.filter (fun e => (Sum.inl e.2 : Sum Nat (Prod Nat Nat)) = x)).card +
    (B.filter (fun e => (Sum.inr e : Sum Nat (Prod Nat Nat)) = x)).card)

def nativePrimeVertexCycleDegree (A : Finset (Prod Nat Nat)) (p : Nat) : Nat :=
  (A.filter (fun e => e.1 = p)).card + (A.filter (fun e => e.2 = p)).card

end PrimeFactorOscillations.FiniteFieldIntegerSignature
