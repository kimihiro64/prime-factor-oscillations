/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassCountProfileLaw
import PrimeFactorOscillations.Helpers.PrimeClassDecoderIntegerProbes
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliDominance
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CapacitySelectionFinite
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PolynomialPrimeNorming

/-!
# Prime-class count laws and finite polynomial decoding

Exports the actual infinite count-profile law with its Euler-product
coefficient identification, exact integer-probe normalization and the
polynomial degree obstruction. Full prime-power component sampling and
the critical decoder capacity theorem remain separate obligations.
-/
