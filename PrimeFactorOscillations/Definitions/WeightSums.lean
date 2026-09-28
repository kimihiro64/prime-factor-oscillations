import PrimeFactorOscillations.Definitions.Reversals
import PrimeFactorUnimodality.Definitions.SymmetricDensity

set_option autoImplicit false

/-!
# Prime-prefix odds sums

The ordinary summand is the canonical Erdos 690 primeWeight. All sums have
the explicit finite support of primes strictly below the natural cutoff x.
-/

namespace PrimeFactorOscillations

noncomputable section

/-- Odds of the generic odd local selection event. -/
def genericOddWeight (p : Nat) : Rat := genericOddEta p / (1 - genericOddEta p)

/-- Ordinary odds summed over the finite prime prefix. -/
def ordinaryPrimeWeightSum (x : Nat) : Rat :=
  ((Finset.range x).filter Nat.Prime).sum PrimeFactorUnimodality.primeWeight

/-- Generic odd odds summed over the same finite prime prefix. -/
def genericOddPrimeWeightSum (x : Nat) : Rat :=
  ((Finset.range x).filter Nat.Prime).sum genericOddWeight

end

end PrimeFactorOscillations
