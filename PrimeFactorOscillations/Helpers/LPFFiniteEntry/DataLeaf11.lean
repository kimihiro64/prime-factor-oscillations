/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.Core

/-! Bounded component of the inclusive finite orbit certificate. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private def lpfEntry10000WitnessRow6563 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 751 2531 6563 [6563] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6569 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2503 7351 6569 [3, 6569] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6571 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 947 2339 6571 [6571] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6577 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1999 7867 6577 [3, 6577] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6581 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1069 8803 6581 [3, 6581] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6599 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 769 2531 6599 [6599] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6607 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1097 2207 6607 [6607] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6619 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 971 2339 6619 [6619] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6637 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 8923 6637 [3, 6637] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6653 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1201 8779 6653 [3, 6653] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6659 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 751 2579 6659 [6659] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6661 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1021 8971 6661 [3, 6661] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6673 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1831 8179 6673 [3, 6673] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6679 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 761 2579 6679 [6679] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6689 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2311 7723 6689 [3, 6689] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6691 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1103 2243 6691 [6691] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6701 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1249 8803 6701 [3, 6701] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6703 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 2579 6703 [6703] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6709 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 997 9067 6709 [3, 6709] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6719 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 829 2531 6719 [6719] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6733 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 9067 6733 [3, 6733] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6737 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 8443 6737 [3, 6737] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6761 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 8059 6761 [3, 6761] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6763 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 971 2411 6763 [6763] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6779 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 811 2579 6779 [6779] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6781 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1201 8971 6781 [3, 6781] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6791 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 929 2467 6791 [6791] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6793 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2179 8011 6793 [3, 6793] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6803 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 823 2579 6803 [6803] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6823 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 881 2531 6823 [6823] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6827 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 883 2531 6827 [6827] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6829 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1153 9091 6829 [3, 6829] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6833 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 8467 6833 [3, 6833] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6841 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 8179 6841 [3, 6841] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6857 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2683 7603 6857 [3, 6857] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6863 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 2731 6863 [6863] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6869 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 9643 6869 [3, 6869] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6871 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 857 2579 6871 [6871] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6883 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 863 2579 6883 [6883] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6899 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 919 2531 6899 [6899] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6907 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1187 2267 6907 [6907] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6911 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 2699 6911 [6911] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6917 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 9643 6917 [3, 6917] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6947 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1063 2411 6947 [6947] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6949 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 877 9547 6949 [3, 6949] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6959 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 2819 6959 [6959] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6961 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 8779 6961 [3, 6961] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6967 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 953 2531 6967 [6967] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6971 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1019 2467 6971 [6971] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6977 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 8803 6977 [3, 6977] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6983 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 2791 6983 [6983] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6991 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 797 2699 6991 [6991] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6997 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 9739 6997 [3, 6997] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7001 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 8419 7001 [3, 7001] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7013 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 877 9643 7013 [3, 7013] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7019 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1163 2347 7019 [7019] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7027 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 983 2531 7027 [7027] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7039 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 2819 7039 [7039] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7043 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 991 2531 7043 [7043] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7057 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 8923 7057 [3, 7057] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7069 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1321 9283 7069 [3, 7069] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7079 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1009 2531 7079 [7079] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7103 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 2851 7103 [7103] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7109 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1021 9643 7109 [3, 7109] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7121 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1759 8923 7121 [3, 7121] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7127 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1097 2467 7127 [7127] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7129 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2683 8011 7129 [3, 7129] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7151 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 2843 7151 [7151] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7159 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1049 2531 7159 [7159] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7177 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2203 8563 7177 [3, 7177] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7187 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1063 2531 7187 [7187] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7193 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 8707 7193 [3, 7193] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7207 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 2903 7207 [7207] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7211 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1259 2347 7211 [7211] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7213 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1753 9067 7213 [3, 7213] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

def lpfEntry10000WitnessLeaf11 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6563 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6569 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6571 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6577 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6581 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6599 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6607 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6619 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6637 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow6653 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6659 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6661 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6673 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6679 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6689 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6691 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6701 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6703 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow6709 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6719 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6733 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6737 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6761 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6763 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6779 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6781 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6791 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6793 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow6803 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6823 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6827 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6829 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6833 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6841 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6857 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6863 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6869 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow6871 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6883 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6899 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6907 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6911 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6917 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6947 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6949 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6959 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6961 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow6967 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6971 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6977 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6983 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6991 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6997 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7001 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7013 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7019 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow7027 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7039 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7043 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7057 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7069 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow7079 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7103 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7109 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7121 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7127 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow7129 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7151 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7159 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7177 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7187 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow7193 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7207 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7211 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7213 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
