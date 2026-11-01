/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeCycleRows

/-! # The strict four-cycle used in signed native sharpness -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativePrimeFourCycle (p q r s : Nat) : Finset (Prod Nat Nat) :=
  {(p, q), (q, r), (r, s), (p, s)}

end PrimeFactorOscillations.FiniteFieldIntegerSignature
