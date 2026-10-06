/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Fin

/-! # The polynomial with consecutive positive integral roots -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace PrimeFactorOscillations

def consecutiveRootValue (d : Nat) {R : Type*} [CommRing R] (a : R) : R :=
  Finset.univ.prod (fun i : Fin d => a - ((i.val + 1 : Nat) : R))

end PrimeFactorOscillations
