/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf00
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf01
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf02
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf03
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf04
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf05
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf06
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.DataLeaf07

/-! Bounded component of the inclusive finite orbit certificate. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private def lpfEntry10000WitnessRow397 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 73 523 397 [3, 397] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow907 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 227 227 907 [907] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1459 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 647 1459 [1459] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2039 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 113 907 2039 [2039] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2663 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 1103 2663 [2663] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3299 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 353 1297 3299 [3299] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3907 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1511 3907 [3907] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

def lpfEntry10000WitnessGroupA : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node lpfEntry10000WitnessLeaf0
  lpfEntry10000WitnessRow397 lpfEntry10000WitnessLeaf1)
  lpfEntry10000WitnessRow907 (OrbitWitnessTree.node lpfEntry10000WitnessLeaf2
  lpfEntry10000WitnessRow1459 lpfEntry10000WitnessLeaf3))
  lpfEntry10000WitnessRow2039 (OrbitWitnessTree.node (OrbitWitnessTree.node lpfEntry10000WitnessLeaf4
  lpfEntry10000WitnessRow2663 lpfEntry10000WitnessLeaf5)
  lpfEntry10000WitnessRow3299 (OrbitWitnessTree.node lpfEntry10000WitnessLeaf6
  lpfEntry10000WitnessRow3907 lpfEntry10000WitnessLeaf7)))

end PrimeFactorOscillations.LPF
