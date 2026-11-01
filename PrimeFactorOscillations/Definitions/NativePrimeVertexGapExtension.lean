/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeVertexGapIndependent

/-! # Finite full-relation rejection test for a new prime vertex -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativePrimeVertexGapExtensionClear (P : Finset Nat) (q : Nat) : Prop :=
  forall O : Finset (Sum Nat (Prod Nat Nat)),
    Membership.mem (nativeVertexGapBasis P).powerset O ->
      forall T : Finset Nat, Membership.mem P.powerset T -> T.Nonempty ->
        Not (IsSquare (O.prod nativeVertexGapValue * T.prod (fun p => q - p)))

instance nativePrimeVertexGapExtensionClearDecidable (P : Finset Nat) (q : Nat) :
    Decidable (nativePrimeVertexGapExtensionClear P q) := by
  unfold nativePrimeVertexGapExtensionClear
  set_option synthInstance.maxSize 8192 in infer_instance

end PrimeFactorOscillations.FiniteFieldIntegerSignature
