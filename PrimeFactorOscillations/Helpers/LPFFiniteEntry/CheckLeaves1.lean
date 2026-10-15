/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataRoot

/-! Bounded component of the inclusive finite orbit certificate. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpfEntry10000WitnessLeaf4_check :
    orbitTreeAll (fun w => decide (ValidTreeOrbitWitness lpfEntry10000WitnessTree w)) lpfEntry10000WitnessLeaf4 = true := by decide

theorem lpfEntry10000WitnessLeaf5_check :
    orbitTreeAll (fun w => decide (ValidTreeOrbitWitness lpfEntry10000WitnessTree w)) lpfEntry10000WitnessLeaf5 = true := by decide

theorem lpfEntry10000WitnessLeaf6_check :
    orbitTreeAll (fun w => decide (ValidTreeOrbitWitness lpfEntry10000WitnessTree w)) lpfEntry10000WitnessLeaf6 = true := by decide

theorem lpfEntry10000WitnessLeaf7_check :
    orbitTreeAll (fun w => decide (ValidTreeOrbitWitness lpfEntry10000WitnessTree w)) lpfEntry10000WitnessLeaf7 = true := by decide

end PrimeFactorOscillations.LPF
