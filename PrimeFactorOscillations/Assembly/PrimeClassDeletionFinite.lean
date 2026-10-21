/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderComplexError
import PrimeFactorOscillations.Helpers.PrimeClassDecoderIntegerProbes
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliDominance
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CapacitySelectionFinite
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PolynomialPrimeNorming

/-!
# Prime-class count laws and finite polynomial decoding

Exports the actual infinite count-profile law, the full uniform
complex-disc error for the literal integer cutoffs, exact integer-probe
normalization and the polynomial degree obstruction. The half-integer
signal, full prime-power component law and critical decoder capacity
remain separate obligations.
-/
