/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeCycleRows

/-! # Computable even-sized Eulerian masks of a finite prime graph

The finite filter equality implements the bounded vertex test without
introducing a classical decision procedure.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativeEvenCycleMasks (P : Finset Nat) (G : Finset (Prod Nat Nat)) :
    Finset (Finset (Prod Nat Nat)) :=
  G.powerset.filter (fun C => And
    (P.filter (fun p => nativePrimeVertexCycleDegree C p % 2 = 0) = P)
    (C.card % 2 = 0))

def nativeEvenCycleCount (P : Finset Nat) (G : Finset (Prod Nat Nat)) : Nat :=
  (nativeEvenCycleMasks P G).card

end PrimeFactorOscillations.FiniteFieldIntegerSignature
