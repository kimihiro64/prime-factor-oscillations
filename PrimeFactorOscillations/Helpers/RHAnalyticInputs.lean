/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPrimePowerAsymptotic
import PrimeFactorOscillations.Helpers.NicolasSharpTangent
import PrimeFactorOscillations.Helpers.NicolasSpatialClock
import PrimeFactorOscillations.Helpers.NicolasTiltedSpectral
import PrimeFactorOscillations.Helpers.NicolasTiltedTail
import PrimeFactorOscillations.Helpers.PrimeProfileAll
import PrimeFactorOscillations.Helpers.PrimeProfileAscentEligibility
import PrimeFactorOscillations.Helpers.PrimeProfileLogSeries
import PrimeFactorOscillations.Helpers.PrimeProfilePowerExcursions
import PrimeFactorOscillations.Helpers.PrimeProfileSpatialThreshold

/-!
# The moving-rank RH equivalence

Exports the corrected theta integral, the exact prime-product clock, and the
moving-rank density-ratio criterion, with both directions of their RH equivalences.
The proof retains Nicolas's finite logarithm and its prime-square correction.
Also exports the unconditional uniform ratio linearization with its exact clock error
and the simultaneous RH comparison on every fixed compact positive rank band,
together with its actual ordinary-ascent reference threshold and the unconditional
existence and local uniqueness of the reference level crossing points.
The actual density ratios have both spatial sign tests outside a logarithmic
buffer, in the stated local rank band and fixed clock comparability window.
The full psi and theta spectral terms have explicit uniform remainders,
including the two-sided estimate for the leading prime-square contribution.
The full prime-power tail also has the leading coefficient two unconditionally.
The positive tilted prime products have the same RH criterion, including
one eventual cutoff for all positive tilts simultaneously. Their signed
logarithmic tail error lies between minus tilt squared over cutoff and
tilt over cutoff for every nonnegative tilt.
The complete absolutely convergent logarithmic tail has its exact prime
support and the two signs on either side of tilt one.
Each fixed positive tilt's weighted theta integral has the RH criterion,
with an explicit error from the base integral bounded by a constant over x log x.
Its RH expansion retains the full zero wave and the leading prime-square bias,
with an explicit normalized error tending to zero for every fixed nonnegative tilt.
Every admissible zero-dependent exponent gives unbounded excursions of both signs
for the psi, theta and fixed-positive-tilt integrals under the stated zero hypothesis.
These centered comparisons alone supply no new bounded prime gaps or raw ascents.
-/
