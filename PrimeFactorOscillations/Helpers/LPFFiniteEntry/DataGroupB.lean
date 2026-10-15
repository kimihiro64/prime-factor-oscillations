/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf08
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf09
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf10
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf11
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf12
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf13
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf14
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf15

/-! Bounded component of the inclusive finite orbit certificate. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private def lpfEntry10000WitnessRow5209 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 6151 5209 [3, 5209] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5857 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1759 7027 5857 [3, 5857] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6553 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2239 7591 6553 [3, 6553] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7219 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1031 2579 7219 [7219] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7919 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3299 7919 [7919] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8647 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3623 8647 [8647] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9323 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2131 2531 9323 [9323] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

def lpfEntry10000WitnessGroupB : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node lpfEntry10000WitnessLeaf8
  lpfEntry10000WitnessRow5209 lpfEntry10000WitnessLeaf9)
  lpfEntry10000WitnessRow5857 (OrbitWitnessTree.node lpfEntry10000WitnessLeaf10
  lpfEntry10000WitnessRow6553 lpfEntry10000WitnessLeaf11))
  lpfEntry10000WitnessRow7219 (OrbitWitnessTree.node (OrbitWitnessTree.node lpfEntry10000WitnessLeaf12
  lpfEntry10000WitnessRow7919 lpfEntry10000WitnessLeaf13)
  lpfEntry10000WitnessRow8647 (OrbitWitnessTree.node lpfEntry10000WitnessLeaf14
  lpfEntry10000WitnessRow9323 lpfEntry10000WitnessLeaf15)))

end PrimeFactorOscillations.LPF
