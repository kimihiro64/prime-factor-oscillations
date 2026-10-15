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

private def lpfEntry10000WitnessRow4549 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 6163 4549 [3, 4549] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4561 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5179 4561 [3, 4561] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4567 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 2111 4567 [4567] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4583 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 2099 4583 [4583] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4591 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 269 2027 4591 [4591] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4597 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 6163 4597 [3, 4597] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4603 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 683 1619 4603 [4603] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4621 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 6271 4621 [3, 4621] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4637 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 6199 4637 [3, 4637] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4639 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 2087 4639 [4639] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4643 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 599 1723 4643 [4643] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4649 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1951 5023 4649 [3, 4649] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4651 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1823 4651 [4651] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4657 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5323 4657 [3, 4657] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4663 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 2099 4663 [4663] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4673 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5347 4673 [3, 4673] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4679 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 2111 4679 [4679] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4691 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 599 1747 4691 [4691] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4703 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 241 2111 4703 [4703] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4721 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5419 4721 [3, 4721] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4723 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 743 1619 4723 [4723] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4729 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5431 4729 [3, 4729] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4733 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 6367 4733 [3, 4733] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4751 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 349 2027 4751 [4751] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4759 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 2207 4759 [4759] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4783 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 2099 4783 [4783] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4787 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 811 1583 4787 [4787] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4789 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 6451 4789 [3, 4789] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4793 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5527 4793 [3, 4793] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4799 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 2207 4799 [4799] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4801 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1759 5443 4801 [3, 4801] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4813 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 6367 4813 [3, 4813] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4817 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5563 4817 [3, 4817] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4831 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 2243 4831 [4831] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4861 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1021 6271 4861 [3, 4861] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4871 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 2243 4871 [4871] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4877 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1069 6247 4877 [3, 4877] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4889 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1831 5503 4889 [3, 4889] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4903 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 353 2099 4903 [4903] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4909 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 6607 4909 [3, 4909] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4919 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 2267 4919 [4919] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4931 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 599 1867 4931 [4931] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4933 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 6547 4933 [3, 4933] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4937 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2467 2 4937 [4937] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4943 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 2243 4943 [4943] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4951 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 2243 4951 [4951] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4957 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 6679 4957 [3, 4957] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4967 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 2251 4967 [4967] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4969 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5791 4969 [3, 4969] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4973 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 6607 4973 [3, 4973] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4987 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 563 1931 4987 [4987] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4993 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5827 4993 [3, 4993] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4999 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 2267 4999 [4999] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5003 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 691 1811 5003 [5003] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5009 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5851 5009 [3, 5009] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5011 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 2003 5011 [5011] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5021 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 6871 5021 [3, 5021] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5023 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 2339 5023 [5023] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5039 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 2347 5039 [5039] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5051 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 619 1907 5051 [5051] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5059 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 2087 5059 [5059] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5077 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 6883 5077 [3, 5077] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5081 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 5839 5081 [3, 5081] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5087 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 2251 5087 [5087] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5099 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 563 1987 5099 [5099] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5101 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 6619 5101 [3, 5101] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5107 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 2111 5107 [5107] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5113 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 6007 5113 [3, 5113] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5119 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 2267 5119 [5119] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5147 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 2131 5147 [5147] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5153 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 6067 5153 [3, 5153] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5167 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 2411 5167 [5167] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5171 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 599 1987 5171 [5171] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5179 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 2087 5179 [5179] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5189 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 7027 5189 [3, 5189] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5197 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 6763 5197 [3, 5197] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

def lpfEntry10000WitnessLeaf8 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4549 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4561 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4567 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4583 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4591 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4597 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4603 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4621 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4637 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow4639 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4643 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4649 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4651 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4657 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4663 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4673 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4679 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4691 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4703 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow4721 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4723 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4729 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4733 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4751 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4759 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4783 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4787 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4789 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4793 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow4799 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4801 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4813 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4817 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4831 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4861 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4871 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4877 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4889 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow4903 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4909 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4919 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4931 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4933 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4937 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4943 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4951 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4957 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4967 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow4969 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4973 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4987 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4993 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4999 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5003 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5009 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5011 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5021 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow5023 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5039 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5051 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5059 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5077 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5081 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5087 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5099 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5101 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5107 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow5113 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5119 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5147 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5153 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5167 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5171 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5179 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5189 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5197 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
