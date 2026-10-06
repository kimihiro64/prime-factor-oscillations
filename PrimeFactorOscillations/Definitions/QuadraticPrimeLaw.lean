/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.PrimeProfile

/-!
# Nonnegative prime weights with a quadratic perturbation

The condition contains only the local weights. It asserts no prime-gap,
coefficient-sign, or RH conclusion. A zero weight is permitted, including
the field-valued odds of a forced factor that is removed by a rank shift.
The constants belong to one fixed law; there is no uniformity over laws.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

structure QuadraticPrimeLaw where
  weight : Nat.Primes -> Real
  nu : Real
  error : Real
  nu_pos : 0 < nu
  error_nonneg : 0 <= error
  weight_nonneg : forall p, 0 <= weight p
  quadratic_error : forall p,
    abs (weight p - nu * primeProfileWeight (p : Nat)) <=
      error * (primeProfileWeight (p : Nat)) ^ 2

namespace QuadraticPrimeLaw

noncomputable def logFactor (law : QuadraticPrimeLaw) (z : Real) (p : Nat.Primes) : Real :=
  Real.log (1 + law.weight p * z) -
    law.nu * z * Real.log (1 + primeProfileWeight (p : Nat))

noncomputable def logProfile (law : QuadraticPrimeLaw) (z : Real) : Real :=
  tsum (law.logFactor z)

noncomputable def profile (law : QuadraticPrimeLaw) (z : Real) : Real :=
  Real.exp (law.logProfile z)

noncomputable def prefixProduct (law : QuadraticPrimeLaw) (N : Nat) (z : Real) : Real :=
  (primeProfilePrefixSet N).prod (fun p => 1 + law.weight p * z)

noncomputable def logTailConstant (law : QuadraticPrimeLaw) (z : Real) : Real :=
  z ^ 2 * (law.nu + law.error) ^ 2 / 2 + z * law.error + law.nu * z / 2

end QuadraticPrimeLaw

end PrimeFactorOscillations
