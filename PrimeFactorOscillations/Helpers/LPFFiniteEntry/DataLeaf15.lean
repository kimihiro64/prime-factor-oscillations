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

private def lpfEntry10000WitnessRow9337 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4363 9643 9337 [3, 9337] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9341 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4129 9883 9341 [3, 9341] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9343 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 821 3851 9343 [9343] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9349 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4093 9931 9349 [3, 9349] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9371 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2339 2347 9371 [9371] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9377 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4327 9739 9377 [3, 9377] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9391 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3923 9391 [9391] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9397 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4129 9967 9397 [3, 9397] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9403 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1493 3209 9403 [9403] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9413 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4153 9967 9413 [3, 9413] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9419 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2131 2579 9419 [9419] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9421 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4261 9871 9421 [3, 9421] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9431 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3943 9431 [9431] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9433 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4507 9643 9433 [3, 9433] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9437 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4273 9883 9437 [3, 9437] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9439 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 4019 9439 [9439] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9461 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4261 9931 9461 [3, 9461] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9463 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 821 3911 9463 [9463] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9467 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2267 2467 9467 [9467] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9473 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4327 9883 9473 [3, 9473] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9479 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4079 9479 [9479] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9491 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1489 3257 9491 [9491] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9497 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4363 9883 9497 [3, 9497] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9511 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1229 3527 9511 [9511] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9521 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4639 9643 9521 [3, 9521] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9533 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4441 9859 9533 [3, 9533] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9539 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1321 3449 9539 [9539] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9547 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2243 2531 9547 [9547] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9551 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 4019 9551 [9551] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9587 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1657 3137 9587 [9587] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9601 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4519 9883 9601 [3, 9601] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9613 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4513 9907 9613 [3, 9613] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9619 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1361 3449 9619 [9619] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9623 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 4111 9623 [9623] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9629 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4513 9931 9629 [3, 9629] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9631 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 797 4019 9631 [9631] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9643 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2243 2579 9643 [9643] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9649 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4591 9883 9649 [3, 9649] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9661 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4561 9931 9661 [3, 9661] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9677 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4549 9967 9677 [3, 9677] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9679 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 4139 9679 [9679] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9689 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4651 9883 9689 [3, 9689] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9697 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4663 9883 9697 [3, 9697] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9719 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 4159 9719 [9719] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9721 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 5659 8923 9721 [3, 9721] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9733 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4729 9871 9733 [3, 9733] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9739 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2339 2531 9739 [9739] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9743 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4211 9743 [9743] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9749 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4657 9967 9749 [3, 9749] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9767 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 4127 9767 [9767] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9769 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 5011 9643 9769 [3, 9769] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9781 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4789 9883 9781 [3, 9781] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9787 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1637 3257 9787 [9787] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9791 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 4139 9791 [9791] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9803 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 4201 9803 [9803] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9811 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1697 3209 9811 [9811] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9817 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4987 9739 9817 [3, 9817] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9829 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4813 9931 9829 [3, 9829] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9833 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 5011 9739 9833 [3, 9833] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9839 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4259 9839 [9839] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9851 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2347 2579 9851 [9851] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9857 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 4903 9883 9857 [3, 9857] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9859 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1481 3449 9859 [9859] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9871 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 797 4139 9871 [9871] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9883 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2411 2531 9883 [9883] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9887 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4283 9887 [9887] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9901 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4969 9883 9901 [3, 9901] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9907 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1697 3257 9907 [9907] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9923 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 3299 9923 [9923] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9929 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 5011 9883 9929 [3, 9929] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9931 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1709 3257 9931 [9931] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9941 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4969 2 9941 [9941] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9949 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4957 9967 9949 [3, 9949] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow9967 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 4283 9967 [9967] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow9973 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 4993 9967 9973 [3, 9973] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

def lpfEntry10000WitnessLeaf15 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9337 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9341 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9343 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9349 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9371 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9377 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9391 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9397 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9403 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow9413 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9419 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9421 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9431 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9433 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9437 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9439 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9461 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9463 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow9467 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9473 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9479 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9491 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9497 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9511 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9521 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9533 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9539 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9547 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow9551 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9587 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9601 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9613 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9619 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9623 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9629 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9631 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9643 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow9649 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9661 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9677 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9679 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9689 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9697 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9719 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9721 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9733 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9739 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow9743 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9749 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9767 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9769 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9781 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9787 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9791 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9803 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9811 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow9817 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9829 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9833 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9839 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9851 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9857 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9859 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9871 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9883 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9887 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow9901 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9907 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9923 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9929 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9931 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow9941 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9949 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow9967 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow9973 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
