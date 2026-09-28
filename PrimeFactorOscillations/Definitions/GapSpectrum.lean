import PrimeFactorOscillations.Definitions.GapFrequency

/-! # The spectrum of actual bounded prime-gap frequencies -/

set_option autoImplicit false

namespace PrimeFactorOscillations

noncomputable section

/-- The proposed sharp rate, formed from actual prime-gap frequency exponents.
Positivity hypotheses on nu belong to its comparison theorems. -/
def primeGapSpectrum (nu : Real) : Real :=
  sSup (Set.range (fun j : Nat =>
    primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + nu)))

end

end PrimeFactorOscillations
