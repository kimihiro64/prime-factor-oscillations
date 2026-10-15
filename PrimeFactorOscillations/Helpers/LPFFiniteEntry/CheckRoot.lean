/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.CheckGroupA
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.CheckGroupB

/-! Bounded component of the inclusive finite orbit certificate. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpfEntry10000WitnessTree_check : orbitTreeCheck lpfEntry10000WitnessTree = true := by
  simp only [orbitTreeCheck, lpfEntry10000WitnessTree, orbitTreeAll, Bool.and_eq_true]
  exact And.intro (by decide)
    (And.intro lpfEntry10000WitnessGroupA_check lpfEntry10000WitnessGroupB_check)

end PrimeFactorOscillations.LPF
