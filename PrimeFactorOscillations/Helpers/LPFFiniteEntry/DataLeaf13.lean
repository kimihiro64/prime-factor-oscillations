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

private def lpfEntry10000WitnessRow7927 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3191 7927 [7927] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7933 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2017 9883 7933 [3, 7933] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7937 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3343 8563 7937 [3, 7937] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7949 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2281 9643 7949 [3, 7949] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7951 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3203 7951 [7951] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7963 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1451 2531 7963 [7963] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7993 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2707 9283 7993 [3, 7993] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8009 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2371 9643 8009 [3, 8009] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8011 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1427 2579 8011 [8011] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8017 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2143 9883 8017 [3, 8017] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8039 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3359 8039 [8039] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8053 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2437 9643 8053 [3, 8053] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8059 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1451 2579 8059 [8059] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8069 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 2221 9883 8069 [3, 8069] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8081 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2239 9883 8081 [3, 8081] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8087 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3343 8087 [8087] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8089 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2851 9283 8089 [3, 8089] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8093 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2593 9547 8093 [3, 8093] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8101 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2269 9883 8101 [3, 8101] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8111 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 3323 8111 [8111] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8117 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2437 9739 8117 [3, 8117] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8123 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1483 2579 8123 [8123] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8147 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1543 2531 8147 [8147] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8161 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2503 9739 8161 [3, 8161] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8167 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1061 3023 8167 [8167] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8171 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1619 2467 8171 [8171] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8179 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1511 2579 8179 [8179] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8191 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3323 8191 [8191] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8209 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2671 9643 8209 [3, 8209] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8219 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1531 2579 8219 [8219] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8221 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2593 9739 8221 [3, 8221] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8231 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 3359 8231 [8231] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8233 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2707 9643 8233 [3, 8233] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8237 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2473 9883 8237 [3, 8237] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8243 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1543 2579 8243 [8243] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8263 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3359 8263 [8263] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8269 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2521 9883 8269 [3, 8269] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8273 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2671 9739 8273 [3, 8273] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8287 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3371 8287 [8287] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8291 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1567 2579 8291 [8291] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8293 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 2557 9883 8293 [3, 8293] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8297 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2707 9739 8297 [3, 8297] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8311 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 797 3359 8311 [8311] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8317 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2593 9883 8317 [3, 8317] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8329 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2851 9643 8329 [3, 8329] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8353 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2647 9883 8353 [3, 8353] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8363 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1931 2251 8363 [8363] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8369 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2671 9883 8369 [3, 8369] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8377 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2683 9883 8377 [3, 8377] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8387 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1847 2347 8387 [8387] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8389 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 2677 9907 8389 [3, 8389] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8419 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1871 2339 8419 [8419] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8423 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3511 8423 [8423] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8429 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3001 9643 8429 [3, 8429] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8431 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1013 3203 8431 [8431] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8443 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1811 2411 8443 [8443] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8447 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 3491 8447 [8447] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8461 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3049 9643 8461 [3, 8461] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8467 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1823 2411 8467 [8467] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8501 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3109 9643 8501 [3, 8501] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8513 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2887 9883 8513 [3, 8513] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8521 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3499 9283 8521 [3, 8521] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8527 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3491 8527 [8527] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8537 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3067 9739 8537 [3, 8537] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8539 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1931 2339 8539 [8539] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8543 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3571 8543 [8543] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8563 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1871 2411 8563 [8563] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8573 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3121 9739 8573 [3, 8573] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8581 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3061 9811 8581 [3, 8581] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8597 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3037 9859 8597 [3, 8597] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8599 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3527 8599 [8599] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8609 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3271 9643 8609 [3, 8609] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8623 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3539 8623 [8623] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8627 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1847 2467 8627 [8627] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow8629 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 9 3037 9907 8629 [3, 8629] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow8641 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 3079 9883 8641 [3, 8641] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

def lpfEntry10000WitnessLeaf13 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7927 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7933 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7937 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7949 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow7951 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7963 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7993 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8009 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8011 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow8017 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8039 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8053 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8059 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8069 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow8081 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8087 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8089 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8093 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8101 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow8111 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8117 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8123 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8147 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8161 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow8167 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8171 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8179 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8191 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8209 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow8219 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8221 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8231 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8233 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8237 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow8243 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8263 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8269 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8273 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow8287 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8291 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8293 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8297 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8311 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow8317 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8329 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8353 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8363 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8369 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow8377 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8387 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8389 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8419 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8423 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow8429 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8431 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8443 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8447 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow8461 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8467 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8501 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8513 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8521 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow8527 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8537 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8539 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8543 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8563 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow8573 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8581 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8597 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8599 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8609 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow8623 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8627 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow8629 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow8641 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
