/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.AffineRatioRH
import PrimeFactorOscillations.Helpers.ConsecutiveRootZeroFree
import PrimeFactorOscillations.Helpers.DoublePrimeAdditionCriterion
import PrimeFactorOscillations.Helpers.FamilyIntervalTransfer
import PrimeFactorOscillations.Helpers.FamilyPrimeCombinations
import PrimeFactorOscillations.Helpers.FixedTiltCombinations
import PrimeFactorOscillations.Helpers.LogarithmicRootCriterion
import PrimeFactorOscillations.Helpers.ModifiedLcmCriticalWindow
import PrimeFactorOscillations.Helpers.PrimeLogReferenceCriterion
import PrimeFactorOscillations.Helpers.QuadraticMassRH
import PrimeFactorOscillations.Helpers.QuadraticProfileCanonicalLinearization
import PrimeFactorOscillations.Helpers.QuadraticProfileScale

/-!
# RH criteria and reference constants across qualifying families

Exports the quadratic local-law criteria, exact probability-mass consumers,
actual affine families, and the generalized reference-scale constants.
-/
