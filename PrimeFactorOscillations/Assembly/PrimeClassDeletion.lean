/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.PrimeClassDeletionFinite
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CapacitySelection
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedSupportFunction
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CriticalCellScale
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianRecordExponents
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeRealCutoffs
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyRegulator
import PrimeFactorOscillations.Proof.PrimeClassDeletion.OverweightSlack
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PartialCapacityCounts
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PositiveDirichletBoundary
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PositiveDirichletContinuation
import PrimeFactorOscillations.Proof.PrimeClassDeletion.RepairHellinger

/-!
# Prime capacities and positive Dirichlet continuation

Exports capped capacities, signed overweight contacts, actual-node polynomial
interpolation and derivative bounds, positive Dirichlet convergence and boundary
summability, and the finite signed Hellinger-energy and deleted-prime counts.
Integral moment geometry and Euler adapters retain their ordinary paper proofs.
-/
