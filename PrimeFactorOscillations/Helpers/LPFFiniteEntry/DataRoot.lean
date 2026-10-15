/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataGroupA
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataGroupB

/-! Bounded component of the inclusive finite orbit certificate. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private def lpfEntry10000WitnessRow4547 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 691 1583 4547 [4547] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

def lpfEntry10000WitnessTree : OrbitWitnessTree :=
  (OrbitWitnessTree.node lpfEntry10000WitnessGroupA
  lpfEntry10000WitnessRow4547 lpfEntry10000WitnessGroupB)

end PrimeFactorOscillations.LPF
