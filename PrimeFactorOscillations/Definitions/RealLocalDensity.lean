import Mathlib.Data.Finset.Card
import PrimeFactorOscillations.Definitions.ReciprocalSmoothLaw
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliMass
import PrimeFactorUnimodality.Definitions.KthPrimeFactor

/-! # Exact real local-rank densities and finite prime prefixes -/

set_option autoImplicit false

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

noncomputable section

/-- The independent probability coordinates at primes strictly below p. -/
def prefixProbabilities (law : ReciprocalSmoothLaw) (p : Nat) : List Real :=
  (((Finset.range p).filter Nat.Prime).toList.map law.eta)

/-- The exact finite coefficient at a strict prime cutoff. -/
def prefixMass (law : ReciprocalSmoothLaw) (p r : Nat) : Real :=
  List.bernoulliMass (law.prefixProbabilities p) r

/-- The real local-law formula for the k-th smallest distinct prime factor.
An arithmetic ensemble interpretation requires a separate independence proof. -/
def rankDensityAt (law : ReciprocalSmoothLaw) (k p : Nat) : Real :=
  law.eta p * law.prefixMass p (k - 1)

/-- The real local-rank density along the canonical increasing prime sequence. -/
def rankDensity (law : ReciprocalSmoothLaw) (k i : Nat) : Real :=
  law.rankDensityAt k (PrimeFactorUnimodality.primeAt i)

end

end PrimeFactorOscillations.ReciprocalSmoothLaw
