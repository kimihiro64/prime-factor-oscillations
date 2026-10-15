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

private def lpfEntry10000WitnessRow3301 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 4219 3301 [3, 3301] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3307 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1151 3307 [3307] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3313 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 3307 3313 [3, 3313] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3319 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1487 3319 [3319] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3323 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 599 1063 3323 [3323] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3329 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 2 3329 [3329] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3331 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1223 3331 [3331] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3343 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1499 3343 [3343] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3347 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1231 3347 [3347] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3359 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1487 3359 [3359] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3361 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 3259 3361 [3, 3361] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3371 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 389 1297 3371 [3371] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3373 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 4327 3373 [3, 3373] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3389 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4423 3389 [3, 3389] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3391 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1523 3391 [3391] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3407 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1531 3407 [3407] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3413 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 4363 3413 [3, 3413] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3433 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1093 4057 3433 [3, 3433] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3449 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1723 2 3449 [3449] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3457 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1489 3697 3457 [3, 3457] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3461 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 4339 3461 [3, 3461] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3463 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1559 3463 [3463] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3467 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1291 3467 [3467] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3469 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 4447 3469 [3, 3469] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3491 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1303 3491 [3491] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3499 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1307 3499 [3499] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3511 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1583 3511 [3511] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3517 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 4519 3517 [3, 3517] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3527 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1571 3527 [3527] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3529 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1093 4201 3529 [3, 3529] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3533 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4639 3533 [3, 3533] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3539 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1327 3539 [3539] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3541 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4651 3541 [3, 3541] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3547 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 557 1217 3547 [3547] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3557 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 4603 3557 [3, 3557] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3559 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1607 3559 [3559] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3571 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1283 3571 [3571] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3581 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 4639 3581 [3, 3581] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3583 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1619 3583 [3583] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3593 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1213 4177 3593 [3, 3593] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3607 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 1571 3607 [3607] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3613 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4759 3613 [3, 3613] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3617 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1249 4177 3617 [3, 3617] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3623 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1619 3623 [3623] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3631 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 1583 3631 [3631] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3637 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 4723 3637 [3, 3637] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3643 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1319 3643 [3643] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3659 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1327 3659 [3659] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3671 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 1607 3671 [3671] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3673 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1453 4057 3673 [3, 3673] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3677 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 4783 3677 [3, 3677] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3691 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 563 1283 3691 [3691] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3697 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1847 2 3697 [3697] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3701 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 4519 3701 [3, 3701] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3709 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4903 3709 [3, 3709] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3719 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1667 3719 [3719] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3727 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 1571 3727 [3727] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3733 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 877 4723 3733 [3, 3733] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3739 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1427 3739 [3739] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3761 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1879 2 3761 [3761] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3767 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 313 1571 3767 [3767] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3769 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1453 4201 3769 [3, 3769] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3779 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1447 3779 [3779] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3793 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1489 4201 3793 [3, 3793] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3797 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 4663 3797 [3, 3797] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3803 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1459 3803 [3803] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3821 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 4999 3821 [3, 3821] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3823 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 1619 3823 [3823] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3833 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1549 4201 3833 [3, 3833] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3847 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 317 1607 3847 [3847] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3851 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1483 3851 [3851] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3853 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 5119 3853 [3, 3853] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3863 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 1699 3863 [3863] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3877 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 5059 3877 [3, 3877] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3881 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1621 4201 3881 [3, 3881] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3889 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1657 4177 3889 [3, 3889] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

def lpfEntry10000WitnessLeaf6 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3301 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3307 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3313 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3319 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3323 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3329 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3331 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3343 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3347 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow3359 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3361 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3371 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3373 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3389 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3391 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3407 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3413 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3433 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3449 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow3457 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3461 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3463 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3467 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3469 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3491 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3499 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3511 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3517 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3527 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow3529 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3533 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3539 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3541 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3547 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3557 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3559 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3571 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3581 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow3583 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3593 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3607 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3613 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3617 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3623 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3631 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3637 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3643 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3659 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow3671 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3673 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3677 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3691 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3697 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3701 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3709 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3719 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3727 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow3733 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3739 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3761 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3767 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3769 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3779 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3793 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3797 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3803 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3821 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow3823 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3833 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3847 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3851 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3853 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3863 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3877 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3881 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3889 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
