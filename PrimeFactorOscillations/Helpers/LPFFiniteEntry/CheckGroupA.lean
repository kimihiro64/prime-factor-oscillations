/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.CheckLeaves0
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.CheckLeaves1

/-! Bounded component of the inclusive finite orbit certificate. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpfEntry10000WitnessGroupA_check :
    orbitTreeAll (fun w => decide (ValidTreeOrbitWitness lpfEntry10000WitnessTree w)) lpfEntry10000WitnessGroupA = true := by
  simp only [lpfEntry10000WitnessGroupA, orbitTreeAll, Bool.and_eq_true]
  exact (And.intro (by decide) (And.intro (And.intro (by decide) (And.intro (And.intro (by decide) (And.intro lpfEntry10000WitnessLeaf0_check lpfEntry10000WitnessLeaf1_check)) (And.intro (by decide) (And.intro lpfEntry10000WitnessLeaf2_check lpfEntry10000WitnessLeaf3_check)))) (And.intro (by decide) (And.intro (And.intro (by decide) (And.intro lpfEntry10000WitnessLeaf4_check lpfEntry10000WitnessLeaf5_check)) (And.intro (by decide) (And.intro lpfEntry10000WitnessLeaf6_check lpfEntry10000WitnessLeaf7_check))))))

end PrimeFactorOscillations.LPF
