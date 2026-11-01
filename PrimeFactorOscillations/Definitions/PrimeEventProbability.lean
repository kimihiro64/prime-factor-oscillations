/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.PrimePairEnsemble

/-! # A canonical actual-prime event frequency

The decision procedure is internal. Equivalent event counts can therefore
be transported without changing the observable or the sampled prime domain.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

noncomputable def primeEventProbability (N : Nat) (P : Nat -> Prop) : Real :=
  ((@Finset.filter Nat P (fun n => Classical.propDecidable (P n))
    (Nat.primesLE N)).card : Real) / (Nat.primeCounting N : Real)

end PrimeFactorOscillations
