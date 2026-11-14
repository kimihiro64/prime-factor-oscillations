/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteDeterminant
import PrimeFactorOscillations.Helpers.HamiltonianMinorPolynomial
import PrimeFactorOscillations.Helpers.HamiltonianRankOneDeterminant
import PrimeFactorOscillations.Helpers.HamiltonianRankOnePole
import PrimeFactorOscillations.Helpers.HamiltonianRectangularMinors
import PrimeFactorOscillations.Helpers.HamiltonianSignedGramMoments
import PrimeFactorOscillations.Helpers.HamiltonianStochasticEnergy
import PrimeFactorOscillations.Helpers.HamiltonianStochasticParity
import PrimeFactorOscillations.Helpers.HamiltonianSubsetCancellation

/-! # Finite inputs to signed Hamiltonian comparison

Exports the checked subset cancellation, actual principal-minor generating
polynomials, the actual signed two-support squared-minor cancellation,
rank-one pole cancellation, and centered stochastic energy bounds.
The analytic occupancy bounds, uniform
permanent remainder and arithmetic counting theorems remain separate proof
obligations; this facade does not assert those headline conclusions.
-/
