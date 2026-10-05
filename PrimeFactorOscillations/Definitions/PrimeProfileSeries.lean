/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Helpers.ComplexAnalysis.CauchyTaylor
import PrimeFactorOscillations.Definitions.PrimeProfile

/-!
# Real coefficients of the prime profile

The real parts of the canonical factorial-normalized complex Taylor coefficients.
-/

set_option autoImplicit false

namespace PrimeFactorOscillations

open BombieriVinogradov.ComplexAnalysis

noncomputable def primeProfileRealCoefficient (j : Nat) : Real :=
  (taylorCoefficient primeProfile 0 j).re

end PrimeFactorOscillations

