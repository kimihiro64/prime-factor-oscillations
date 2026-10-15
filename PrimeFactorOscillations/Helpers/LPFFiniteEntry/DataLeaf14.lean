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

private def lpfEntry10000WitnessRow8663 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3671 8663 [8663] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8669 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3121 9883 8669 [3, 8669] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8677 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3109 9907 8677 [3, 8677] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8681 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3739 9283 8681 [3, 8681] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8689 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3391 9643 8689 [3, 8689] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8693 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3109 9931 8693 [3, 8693] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8699 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2003 2347 8699 [8699] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8707 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1823 2531 8707 [8707] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8713 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3187 9883 8713 [3, 8713] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8719 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3659 8719 [8719] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8731 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1787 2579 8731 [8731] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8737 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3463 9643 8737 [3, 8737] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8741 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3181 9931 8741 [3, 8741] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8747 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1907 2467 8747 [8747] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8753 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3391 9739 8753 [3, 8753] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8761 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3259 9883 8761 [3, 8761] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8779 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1811 2579 8779 [8779] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8783 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3691 8783 [8783] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8803 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1823 2579 8803 [8803] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8807 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 3671 8807 [8807] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8819 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1153 3257 8819 [8819] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8821 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3301 9931 8821 [3, 8821] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8831 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 3659 8831 [8831] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8837 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3373 9883 8837 [3, 8837] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8839 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3719 8839 [8839] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8849 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3391 9883 8849 [3, 8849] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8861 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4201 9091 8861 [3, 8861] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8863 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3659 8863 [8863] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8867 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2087 2347 8867 [8867] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8887 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3671 8887 [8887] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8893 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3697 9643 8893 [3, 8893] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8923 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1931 2531 8923 [8923] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8929 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3511 9883 8929 [3, 8929] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8933 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3433 9967 8933 [3, 8933] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8941 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3529 9883 8941 [3, 8941] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8951 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 3719 8951 [8951] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8963 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 3449 8963 [8963] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8969 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3571 9883 8969 [3, 8969] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8971 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1907 2579 8971 [8971] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8999 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 3767 8999 [8999] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9001 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4219 9283 9001 [3, 9001] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9007 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3803 9007 [9007] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9011 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2039 2467 9011 [9011] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9013 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3613 9907 9013 [3, 9013] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9029 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3613 9931 9029 [3, 9029] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9041 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3823 9739 9041 [3, 9041] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9043 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2111 2411 9043 [9043] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9049 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3691 9883 9049 [3, 9049] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9059 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1321 3209 9059 [9059] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9067 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2003 2531 9067 [9067] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9091 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2207 2339 9091 [9091] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9103 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3851 9103 [9103] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9109 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3733 9931 9109 [3, 9109] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9127 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3863 9127 [9127] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9133 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4057 9643 9133 [3, 9133] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9137 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3823 9883 9137 [3, 9137] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9151 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3803 9151 [9151] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9157 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3769 9967 9157 [3, 9157] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9161 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4003 9739 9161 [3, 9161] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9173 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3793 9967 9173 [3, 9173] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9181 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3889 9883 9181 [3, 9181] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9187 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1697 2897 9187 [9187] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9199 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 797 3803 9199 [9199] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9203 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1153 3449 9203 [9203] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9209 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3931 9883 9209 [3, 9209] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9221 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4021 9811 9221 [3, 9221] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9227 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2267 2347 9227 [9227] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9239 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3919 9239 [9239] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9241 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4219 9643 9241 [3, 9241] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9257 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4003 9883 9257 [3, 9257] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9277 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4177 9739 9277 [3, 9277] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9281 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4639 2 9281 [9281] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9283 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2111 2531 9283 [9283] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9293 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4057 9883 9293 [3, 9293] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9311 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 3923 9311 [9311] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9319 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 797 3863 9319 [9319] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

def lpfEntry10000WitnessLeaf14 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8663 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8669 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8677 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8681 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow8689 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8693 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8699 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8707 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8713 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow8719 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8731 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8737 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8741 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8747 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow8753 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8761 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8779 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8783 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8803 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow8807 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8819 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8821 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8831 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8837 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow8839 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8849 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8861 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8863 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8867 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow8887 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8893 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8923 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8929 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8933 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow8941 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8951 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8963 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8969 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow8971 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8999 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9001 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9007 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9011 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9013 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9029 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9041 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9043 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9049 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow9059 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9067 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9091 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9103 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9109 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9127 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9133 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9137 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9151 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow9157 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9161 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9173 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9181 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9187 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9199 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9203 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9209 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9221 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9227 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow9239 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9241 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9257 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9277 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9281 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9283 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9293 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9311 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9319 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
