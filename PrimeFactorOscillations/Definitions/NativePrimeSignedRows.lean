/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeCycleRows

/-! # The actual signed native endpoint-gap coefficients -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativeSignedLowerCoefficient (e : Prod Nat Nat) : Int :=
  -((e.1 * (e.2 - e.1) : Nat) : Int)

def nativeSignedUpperCoefficient (e : Prod Nat Nat) : Int :=
  ((e.2 * (e.2 - e.1) : Nat) : Int)

def nativeSignedRowProduct (A B : Finset (Prod Nat Nat)) : Int :=
  A.prod nativeSignedLowerCoefficient * B.prod nativeSignedUpperCoefficient

end PrimeFactorOscillations.FiniteFieldIntegerSignature
