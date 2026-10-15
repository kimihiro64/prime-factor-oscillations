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

private def lpfEntry10000WitnessRow3911 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 1723 3911 [3911] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3917 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 5119 3917 [3, 3917] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3919 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1787 3919 [3919] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3923 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1459 3923 [3923] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3929 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 4231 3929 [3, 3929] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3931 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1523 3931 [3931] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3943 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 353 1619 3943 [3943] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3947 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1531 3947 [3947] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3967 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1811 3967 [3967] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3989 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 5323 3989 [3, 3989] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4001 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 4339 4001 [3, 4001] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4003 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1559 4003 [4003] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4007 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1811 4007 [4007] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4013 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 5167 4013 [3, 4013] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4019 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1567 4019 [4019] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4021 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 5179 4021 [3, 4021] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4027 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1571 4027 [4027] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4049 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1831 4243 4049 [3, 4049] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4051 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1583 4051 [4051] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4057 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2027 2 4057 [4057] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4073 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 4447 4073 [3, 4073] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4079 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1867 4079 [4079] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4091 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1543 4091 [4091] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4093 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 5479 4093 [3, 4093] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4099 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1607 4099 [4099] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4111 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 1823 4111 [4111] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4127 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1871 4127 [4127] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4129 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1831 4363 4129 [3, 4129] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4133 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 5443 4133 [3, 4133] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4139 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1627 4139 [4139] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4153 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 4567 4153 [3, 4153] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4157 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 5503 4157 [3, 4157] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4159 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1907 4159 [4159] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4177 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2087 2 4177 [4177] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4201 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2099 2 4201 [4201] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4211 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 563 1543 4211 [4211] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4217 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 4663 4217 [3, 4217] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4219 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1667 4219 [4219] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4229 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 5683 4229 [3, 4229] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4231 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 269 1847 4231 [4231] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4241 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1759 4603 4241 [3, 4241] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4243 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1619 4243 [4243] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4253 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 5647 4253 [3, 4253] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4259 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1627 4259 [4259] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4261 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 5659 4261 [3, 4261] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4271 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 1907 4271 [4271] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4273 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1759 4651 4273 [3, 4273] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4283 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1699 4283 [4283] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4289 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 4651 4289 [3, 4289] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4297 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 4783 4297 [3, 4297] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4327 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 1931 4327 [4327] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4337 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 4723 4337 [3, 4337] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4339 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1667 4339 [4339] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4349 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 5791 4349 [3, 4349] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4357 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 5779 4357 [3, 4357] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4363 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 563 1619 4363 [4363] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4373 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 5827 4373 [3, 4373] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4391 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 2003 4391 [4391] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4397 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 5839 4397 [3, 4397] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4409 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 4951 4409 [3, 4409] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4421 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 5779 4421 [3, 4421] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4423 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 2039 4423 [4423] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4441 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 4999 4441 [3, 4441] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4447 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 1931 4447 [4447] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4451 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1723 4451 [4451] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4457 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5023 4457 [3, 4457] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4463 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 2039 4463 [4463] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4481 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5059 4481 [3, 4481] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4483 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 659 1583 4483 [4483] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4493 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 6079 4493 [3, 4493] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4507 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1811 4507 [4507] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4513 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 5107 4513 [3, 4513] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4517 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 6043 4517 [3, 4517] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow4519 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 2087 4519 [4519] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow4523 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 563 1699 4523 [4523] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

def lpfEntry10000WitnessLeaf7 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3911 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3917 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3919 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3923 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3929 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3931 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3943 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3947 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3967 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow3989 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4001 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4003 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4007 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4013 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4019 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4021 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4027 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4049 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow4051 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4057 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4073 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4079 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4091 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4093 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4099 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4111 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4127 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4129 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow4133 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4139 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4153 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4157 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4159 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4177 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4201 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4211 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4217 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow4219 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4229 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4231 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4241 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4243 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4253 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4259 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4261 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4271 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4273 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow4283 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4289 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4297 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4327 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4337 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4339 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4349 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4357 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4363 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow4373 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4391 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4397 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4409 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4421 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4423 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4441 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4447 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4451 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4457 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow4463 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4481 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4483 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4493 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4507 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow4513 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4517 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow4519 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow4523 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
