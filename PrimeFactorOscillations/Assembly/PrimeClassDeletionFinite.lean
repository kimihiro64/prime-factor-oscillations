/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderIntegerProbes
import PrimeFactorOscillations.Helpers.PrimeClassSparseDeletion
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliDominance
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CapacitySelectionFinite
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeDivisibility
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeMissingCost
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeExceptionalCoordinate
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PolynomialPrimeNorming
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentBudget
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentClassSeries
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeRecordAllCutoffs

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
are checked. Ordinary integer divisibility has the literal fixed-cutoff
sampling limit with explicit error. Affine probabilities include beta=-2;
affine odds require beta>-2. The exceptional prime2 is removed with its
exact rank shift and positive survival factor. Missing-cost optimality
extends to infinite nonnegative decreasing weights whenever a competitor's
missing cost converges, including the full logarithmic Euler cost.
The actual signed record energy retains its prime supply, ordinary integral,
left limits and terminal correction at every real cutoff. Strict-record
energy bounds imply all-cutoff power bounds with the finite initial record
explicit in the constant. These estimates retain the independent energy
hypothesis. Full-component finite atom counts, exact signed floor errors and
uniform atom error bounds are proved. Summing over arbitrary finite sets of
supported components retains the complete geometric Euler budget, including
every prime power. The infinite prime-power law, its normalization and
independence remain separate obligations.
-/
