/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.CheckRoot

/-! The earlier six-generation prefix, checked against the maintained tree. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace PrimeFactorOscillations.LPF

theorem prime_le_22_mem_fullOrbit_two_4 (p : Nat) (hp : Nat.Prime p)
    (hle : p <= 22) : Membership.mem (fullOrbit {2} 4) p := by
  have hCover : orbitTreeIntervalCheck lpfEntry10000WitnessTree 4 0 23 = true := by
    decide
  exact orbitTreeIntervalCheck_reachable lpfEntry10000WitnessTree
    lpfEntry10000WitnessTree_check 4 0 23 hCover p hp (Nat.zero_le p) (by omega)

theorem prime_le_432_mem_fullOrbit_two_6 (p : Nat) (hp : Nat.Prime p)
    (hle : p <= 432) : Membership.mem (fullOrbit {2} 6) p := by
  have hCover : orbitTreeIntervalCheck lpfEntry10000WitnessTree 6 0 433 = true := by
    decide
  exact orbitTreeIntervalCheck_reachable lpfEntry10000WitnessTree
    lpfEntry10000WitnessTree_check 6 0 433 hCover p hp (Nat.zero_le p) (by omega)

end PrimeFactorOscillations.LPF
