/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.CheckLeaves2
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.CheckLeaves3

/-! Bounded component of the inclusive finite orbit certificate. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpfEntry10000WitnessGroupB_check :
    orbitTreeAll (fun w => decide (ValidTreeOrbitWitness lpfEntry10000WitnessTree w)) lpfEntry10000WitnessGroupB = true := by
  simp only [lpfEntry10000WitnessGroupB, orbitTreeAll, Bool.and_eq_true]
  exact (And.intro (by decide) (And.intro (And.intro (by decide) (And.intro (And.intro (by decide) (And.intro lpfEntry10000WitnessLeaf8_check lpfEntry10000WitnessLeaf9_check)) (And.intro (by decide) (And.intro lpfEntry10000WitnessLeaf10_check lpfEntry10000WitnessLeaf11_check)))) (And.intro (by decide) (And.intro (And.intro (by decide) (And.intro lpfEntry10000WitnessLeaf12_check lpfEntry10000WitnessLeaf13_check)) (And.intro (by decide) (And.intro lpfEntry10000WitnessLeaf14_check lpfEntry10000WitnessLeaf15_check))))))

end PrimeFactorOscillations.LPF
