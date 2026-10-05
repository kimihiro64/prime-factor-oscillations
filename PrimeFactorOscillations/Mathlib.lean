import PrimeFactorOscillations.Mathlib.Algebra.All
import PrimeFactorOscillations.Mathlib.Analysis.All
import PrimeFactorOscillations.Mathlib.Data.All
import PrimeFactorOscillations.Mathlib.NumberTheory.All
import PrimeFactorOscillations.Mathlib.Order.Interval.Finset.NatPeaks
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliAsymptotics
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliPatterns
import PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.LargestWeightHarmonic
import PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.RationalBounds

/-!
# Mathlib candidate facade

This facade imports only reusable modules that are being maintained for eventual
upstreaming to Mathlib. Candidate source belongs under `PrimeFactorOscillations/Mathlib/`
and must remain independent of every project-specific definition, proof branch,
assembly module, and statement surface.

When a real candidate module is added, import it here and record its proposed
upstream path and readiness in `MATHLIB_PORTING.md`.
-/
