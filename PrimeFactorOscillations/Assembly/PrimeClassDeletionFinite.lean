/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderIntegerProbes
import PrimeFactorOscillations.Helpers.PrimeClassSparseDeletion
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliDominance
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CapacitySelectionFinite
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeProbability
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PolynomialPrimeNorming

/-!
# Prime-class count laws and finite polynomial decoding

Exports the actual infinite count-profile law, the full uniform complex-disc
error, the signed half-integer supply and the exact integer prime-label
decoder for the literal cutoffs, together with every prefix count,
executable rational selectors, full preprocessing and evaluation costs,
binary bit guarantees and the polynomial degree obstruction. The exact
critical decoding capacity, convergence/counting exponent identification,
and the missed fraction for arbitrary polynomial coefficients are proved.
Every admissible power also gives the full all-cutoff inverse count bound.
The actual Fermat, Mersenne and Fibonacci prime-value classes have infinite
capacity, with verified finite membership tests and the golden-ratio bound.
Deleting a class of convergence exponent zero preserves every convergent
positive exponent and the decoding capacity on its stated class domain.
The actual capped-prime class has stochastic dominance at every rank,
comparison for every increasing test and both moment ranges, and
coefficientwise extremality for all finite nonnegative decreasing odds.
The finite product law, its exact coefficients and deterministic endpoints
are checked. Affine specializations, infinite missing-product comparison,
the full prime-power component law and RH applications remain separate
obligations.
-/
