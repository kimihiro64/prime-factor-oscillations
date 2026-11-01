/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeCycleRows

/-! # Computable all-Eulerian masks, retaining both cardinality parities -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativeEulerianMasks (P : Finset Nat) (G : Finset (Prod Nat Nat)) :
    Finset (Finset (Prod Nat Nat)) :=
  G.powerset.filter (fun C =>
    P.filter (fun p => nativePrimeVertexCycleDegree C p % 2 = 0) = P)

def nativeEulerianCount (P : Finset Nat) (G : Finset (Prod Nat Nat)) : Nat :=
  (nativeEulerianMasks P G).card

end PrimeFactorOscillations.FiniteFieldIntegerSignature
