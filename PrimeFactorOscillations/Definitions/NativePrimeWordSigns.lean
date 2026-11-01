/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Real.Basic

/-! # Boolean sign assignments and native word selectors -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativeWordSign (b : Bool) : Real := if b then 1 else -1

noncomputable def nativeWordBit (b : Bool) (x : Real) : Real := (1 + nativeWordSign b * x) / 2

end PrimeFactorOscillations.FiniteFieldIntegerSignature
