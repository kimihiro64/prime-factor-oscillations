/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.PrimeProfile

/-!
# Normalized prefixes with one incomplete ordered prime cycle

The finite products retain the canonical exponential compensator. At any
cutoff either every selected block is complete, or a single increasing block
leaves its first and next prime factors. The block containing the cutoff has
multiplicative diameter at most two. No bound on its additive diameter or
number of primes is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- Analytic finite prefixes with the exact one-boundary-factor identity.
Concrete progression transports must separately supply this identity. -/
structure PrimeCyclePrefix where
  complexPrefix : Nat -> Complex -> Complex
  differentiable_complexPrefix : forall N : Nat, Differentiable Complex (complexPrefix N)
  boundary_factor : forall N : Nat, 1 <= N ->
    complexPrefix N = primePrefixProfile N \/
      exists p q : Nat, Nat.Prime p /\ Nat.Prime q /\ p <= N /\ N < q /\
        N <= 2 * p /\ forall z : Complex,
          complexPrefix N z * (1 + (primeProfileWeight p : Complex) * z) =
            primePrefixProfile N z * (1 + (primeProfileWeight q : Complex) * z)

end PrimeFactorOscillations
