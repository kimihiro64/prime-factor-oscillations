/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderExact
import PrimeFactorOscillations.Helpers.PrimeClassDecoderIntegerProbes
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliDominance
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CapacitySelectionFinite
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PolynomialPrimeNorming

/-!
# Prime-class count laws and finite polynomial decoding

Exports the actual infinite count-profile law, the full uniform complex-disc
error, the signed half-integer supply and the exact integer prime-label
decoder for the literal cutoffs, together with the polynomial degree
obstruction. Computation costs, the full prime-power component law and
critical decoder capacity remain separate obligations.
-/
