/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeEvenCycleMasks

/-! # Logical readout and positive supply of computable even-cycle masks -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_even_cycle_masks_mem_iff (P : Finset Nat)
    (G C : Finset (Prod Nat Nat)) :
    Membership.mem (nativeEvenCycleMasks P G) C <->
      And (C <= G) (And
        (forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
        (C.card % 2 = 0)) := by
  rw [nativeEvenCycleMasks, Finset.mem_filter, Finset.mem_powerset]
  constructor
  . intro h
    refine And.intro h.1 (And.intro ?_ h.2.2)
    intro p hp
    have hm : Membership.mem
        (P.filter (fun x => nativePrimeVertexCycleDegree C x % 2 = 0)) p := by
      rw [h.2.1]
      exact hp
    exact (Finset.mem_filter.mp hm).2
  . intro h
    refine And.intro h.1 (And.intro ?_ h.2.2)
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro p hp
    exact Finset.mem_filter.mpr (And.intro hp (h.2.1 p hp))

theorem native_even_cycle_count_positive (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) : 0 < nativeEvenCycleCount P G := by
  have hsub : ({} : Finset (Prod Nat Nat)) <= G := by
    intro e he
    exact False.elim (Finset.notMem_empty e he)
  have hm : Membership.mem (nativeEvenCycleMasks P G) {} := by
    apply (native_even_cycle_masks_mem_iff P G {}).mpr
    refine And.intro hsub (And.intro ?_ ?_)
    . intro p hp
      simp [nativePrimeVertexCycleDegree]
    . simp
  exact Finset.card_pos.mpr (Exists.intro {} hm)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
