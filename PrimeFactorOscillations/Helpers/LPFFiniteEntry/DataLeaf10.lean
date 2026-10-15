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

private def lpfEntry10000WitnessRow5861 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 8059 5861 [3, 5861] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5867 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 683 2251 5867 [5867] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5869 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1201 7603 5869 [3, 5869] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5879 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 409 2531 5879 [5879] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5881 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 7159 5881 [3, 5881] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5897 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1879 6967 5897 [3, 5897] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5903 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 373 2579 5903 [5903] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5923 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 719 2243 5923 [5923] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5927 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 433 2531 5927 [5927] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5939 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 2467 5939 [5939] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5953 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2239 6691 5953 [3, 5953] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5981 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1249 7723 5981 [3, 5981] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5987 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 743 2251 5987 [5987] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6007 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 593 2411 6007 [6007] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6011 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 659 2347 6011 [6011] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6029 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 8011 6029 [3, 6029] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6037 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 877 8179 6037 [3, 6037] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6043 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 2579 6043 [6043] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6047 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 557 2467 6047 [6047] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6053 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 8419 6053 [3, 6053] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6067 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 2531 6067 [6067] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6073 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1759 7351 6073 [3, 6073] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6079 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 461 2579 6079 [6079] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6089 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 7351 6089 [3, 6089] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6091 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 839 2207 6091 [6091] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6101 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 8419 6101 [3, 6101] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6113 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 7507 6113 [3, 6113] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6121 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1831 7351 6121 [3, 6121] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6131 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 599 2467 6131 [6131] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6133 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 8539 6133 [3, 6133] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6143 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 541 2531 6143 [6143] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6151 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 809 2267 6151 [6151] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6163 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 2579 6163 [6163] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6173 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1201 8059 6173 [3, 6173] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6197 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 8563 6197 [3, 6197] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6199 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 521 2579 6199 [6199] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6203 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 691 2411 6203 [6203] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6211 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 839 2267 6211 [6211] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6217 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 7243 6217 [3, 6217] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6221 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1153 8179 6221 [3, 6221] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6229 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 877 8467 6229 [3, 6229] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6247 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 593 2531 6247 [6247] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6257 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 7723 6257 [3, 6257] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6263 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 601 2531 6263 [6263] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6269 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1801 7603 6269 [3, 6269] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6271 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 557 2579 6271 [6271] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6277 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 8563 6277 [3, 6277] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6287 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 613 2531 6287 [6287] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6299 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 619 2531 6299 [6299] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6301 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 8419 6301 [3, 6301] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6311 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 577 2579 6311 [6311] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6317 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 8443 6317 [3, 6317] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6323 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 751 2411 6323 [6323] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6329 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 7411 6329 [3, 6329] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6337 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 7723 6337 [3, 6337] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6343 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 593 2579 6343 [6343] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6353 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 7867 6353 [3, 6353] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6359 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 601 2579 6359 [6359] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6361 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1951 7591 6361 [3, 6361] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6367 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 653 2531 6367 [6367] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6373 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 8803 6373 [3, 6373] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6379 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 659 2531 6379 [6379] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6389 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 8923 6389 [3, 6389] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6397 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 8563 6397 [3, 6397] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6421 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 8971 6421 [3, 6421] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6427 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 683 2531 6427 [6427] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6449 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 8011 6449 [3, 6449] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6451 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 887 2339 6451 [6451] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6469 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 9043 6469 [3, 6469] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6473 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2203 7507 6473 [3, 6473] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6481 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 8059 6481 [3, 6481] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6491 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1039 2207 6491 [6491] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6521 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 7699 6521 [3, 6521] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6529 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 8011 6529 [3, 6529] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow6547 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 743 2531 6547 [6547] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow6551 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 809 2467 6551 [6551] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

def lpfEntry10000WitnessLeaf10 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5861 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5867 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5869 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5879 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5881 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5897 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5903 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5923 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5927 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow5939 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5953 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5981 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5987 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6007 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6011 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6029 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6037 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6043 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6047 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow6053 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6067 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6073 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6079 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6089 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6091 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6101 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6113 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6121 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6131 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow6133 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6143 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6151 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6163 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6173 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6197 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6199 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6203 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6211 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow6217 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6221 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6229 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6247 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6257 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6263 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6269 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6271 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6277 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6287 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow6299 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6301 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6311 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6317 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6323 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6329 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6337 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6343 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6353 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow6359 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6361 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6367 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6373 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6379 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6389 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6397 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6421 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6427 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6449 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow6451 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6469 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6473 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6481 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6491 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow6521 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6529 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow6547 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow6551 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
