/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Helpers.ComplexAnalysis.CauchyTaylor
import PrimeFactorOscillations.Definitions.QuadraticPrimeLaw

/-! # Entire-profile objects for a quadratic prime law -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

noncomputable def complexFactor (law : QuadraticPrimeLaw) (p : Nat.Primes)
    (z : Complex) : Complex :=
  (1 + (law.weight p : Complex) * z) *
    Complex.exp (-((law.nu * Real.log (1 + primeProfileWeight (p : Nat)) : Real) : Complex) * z)

noncomputable def complexProfile (law : QuadraticPrimeLaw) (z : Complex) : Complex :=
  tprod (fun p : Nat.Primes => law.complexFactor p z)

noncomputable def complexPrefix (law : QuadraticPrimeLaw) (N : Nat) (z : Complex) : Complex :=
  (primeProfilePrefixSet N).prod (fun p => law.complexFactor p z)

noncomputable def complexTailConstant (law : QuadraticPrimeLaw) (R : Real) : Real :=
  ((law.error + law.nu / 2) * R + law.nu ^ 2 * R ^ 2 * Real.exp (law.nu * R)) *
    Real.exp (law.nu * R)

noncomputable def realCoefficient (law : QuadraticPrimeLaw) (j : Nat) : Real :=
  (BombieriVinogradov.ComplexAnalysis.taylorCoefficient law.complexProfile 0 j).re

noncomputable def positiveLowerBound (law : QuadraticPrimeLaw) (b : Real) : Real :=
  Real.exp (-(law.logTailConstant b *
    tsum (fun p : Nat.Primes => (primeProfileWeight (p : Nat)) ^ 2)))

end PrimeFactorOscillations.QuadraticPrimeLaw
