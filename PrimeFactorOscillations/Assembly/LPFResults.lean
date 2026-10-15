/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDensePower
import PrimeFactorOscillations.Helpers.LPFDiagonalSeed
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.Result
import PrimeFactorOscillations.Helpers.LPFFrontierCharacter
import PrimeFactorOscillations.Helpers.LPFGoldbachSourceTransfer
import PrimeFactorOscillations.Helpers.LPFLocalizedTransfer
import PrimeFactorOscillations.Helpers.LPFPrimeTargetTail
import PrimeFactorOscillations.Helpers.LPFPrimeTargetTruncated
import PrimeFactorOscillations.Helpers.LPFResidueCounts
import PrimeFactorOscillations.Helpers.LPFResidueObstruction
import PrimeFactorOscillations.Helpers.LPFTotalImageVariance
import PrimeFactorOscillations.Helpers.LPFWeightedCanonicalEnergy

/-!
# Fresh largest-prime-factor distribution results

The exact finite transfers, uniform prime-character input, and complete
smooth-number and LPF character and residue bounds are exported together.
The current full dynamics allows all diagonals and starts from {2,p}. Its
common-orbit and reached-seed reductions are exported. The distinct-input
operator remains a subordinate source of lower bounds; its closed two-point
examples are explicitly historical and do not describe the full dynamics.
No legacy LPF proof module is used.
-/
