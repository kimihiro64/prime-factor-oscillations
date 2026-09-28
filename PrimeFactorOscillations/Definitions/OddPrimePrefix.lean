import PrimeFactorUnimodality.Definitions.KthPrimeFactor

/-! # The prime prefix supporting the generic odd local law -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- The prime prefix after removing the zero-probability prime two. -/
noncomputable def oddPrimesBelow (x : Nat) : List Nat :=
  (PrimeFactorUnimodality.primesBelow x).filter (fun p => decide (2 < p))

end PrimeFactorOscillations
