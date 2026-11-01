/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Prime.Basic

/-! # Indexed prime-vertex and positive-gap square classes

A vertex and a gap remain distinct indices even when their numerical values
coincide. Every square-product test retains its explicit finite support.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

/-- The complete indexed vertex/gap support of a finite vertex set. -/
def nativeVertexGapBasis (P : Finset Nat) : Finset (Sum Nat (Prod Nat Nat)) :=
  Union.union
    (P.image (fun p => (Sum.inl p : Sum Nat (Prod Nat Nat))))
    (((P.product P).filter (fun pq => pq.1 < pq.2)).image
      (fun pq => (Sum.inr pq : Sum Nat (Prod Nat Nat))))

/-- Numerical value at a vertex index or a strict positive-gap index. -/
def nativeVertexGapValue : Sum Nat (Prod Nat Nat) -> Nat
  | Sum.inl p => p
  | Sum.inr pq => pq.2 - pq.1

/-- No nonempty indexed subfamily has square product. The powerset makes the
entire test finite and computable. -/
def nativePrimeVertexGapIndependent (P : Finset Nat) : Prop :=
  forall S : Finset (Sum Nat (Prod Nat Nat)),
    Membership.mem (nativeVertexGapBasis P).powerset S ->
      IsSquare (S.prod nativeVertexGapValue) -> S = {}

instance nativePrimeVertexGapIndependentDecidable (P : Finset Nat) :
    Decidable (nativePrimeVertexGapIndependent P) := by
  unfold nativePrimeVertexGapIndependent
  set_option synthInstance.maxSize 4096 in infer_instance

end PrimeFactorOscillations.FiniteFieldIntegerSignature
