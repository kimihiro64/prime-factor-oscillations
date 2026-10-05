/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Prime.Defs
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.NormalizedLinearProduct

/-!
# Normalized prime profile

Canonical infinite and finite prime products, with the prime two included.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- Reciprocal predecessor weight of a prime. Defined on naturals for finite-prefix use. -/
noncomputable def primeProfileWeight (p : Nat) : Real :=
  1 / ((p - 1 : Nat) : Real)

/-- The entire normalized prime product used by the moving-rank reference. -/
noncomputable def primeProfile (z : Complex) : Complex :=
  tprod (fun p : Nat.Primes =>
    Complex.normalizedLinearFactor (primeProfileWeight (p : Nat)) z)

/-- All primes at most the inclusive natural cutoff. -/
def primeProfilePrefixSet (N : Nat) : Finset Nat.Primes :=
  (Finset.range (N + 1)).subtype Nat.Prime

/-- Finite normalized product over all primes at most the cutoff. -/
noncomputable def primePrefixProfile (N : Nat) (z : Complex) : Complex :=
  (primeProfilePrefixSet N).prod
    (fun p => Complex.normalizedLinearFactor (primeProfileWeight (p : Nat)) z)

end PrimeFactorOscillations

