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

private def lpfEntry10000WitnessRow5227 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 2111 5227 [5227] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5231 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 269 2347 5231 [5231] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5233 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1759 6091 5233 [3, 5233] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5237 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 6823 5237 [3, 5237] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5261 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 7159 5261 [3, 5261] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5273 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 6247 5273 [3, 5273] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5279 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 2467 5279 [5279] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5281 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1759 6163 5281 [3, 5281] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5297 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 6163 5297 [3, 5297] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5303 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 241 2411 5303 [5303] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5309 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 997 6967 5309 [3, 5309] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5323 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 563 2099 5323 [5323] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5333 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 7243 5333 [3, 5333] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5347 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 563 2111 5347 [5347] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5351 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 409 2267 5351 [5351] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5381 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 7411 5381 [3, 5381] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5387 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 2251 5387 [5387] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5393 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 6427 5393 [3, 5393] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5399 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 2467 5399 [5399] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5407 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 2531 5407 [5407] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5413 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 7459 5413 [3, 5413] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5417 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1759 6367 5417 [3, 5417] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5419 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 2267 5419 [5419] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5431 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 449 2267 5431 [5431] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5437 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 997 7159 5437 [3, 5437] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5441 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 6379 5441 [3, 5441] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5443 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 683 2039 5443 [5443] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5449 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1831 6343 5449 [3, 5449] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5471 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 269 2467 5471 [5471] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5477 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 7459 5477 [3, 5477] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5479 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 401 2339 5479 [5479] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5483 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 643 2099 5483 [5483] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5501 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 7591 5501 [3, 5501] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5503 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 2579 5503 [5503] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5507 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 2251 5507 [5507] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5519 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 2531 5519 [5519] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5521 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 6619 5521 [3, 5521] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5527 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 2531 5527 [5527] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5531 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 739 2027 5531 [5531] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5557 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 7603 5557 [3, 5557] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5563 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 2339 5563 [5563] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5569 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 6691 5569 [3, 5569] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5573 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 7699 5573 [3, 5573] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5581 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1021 7351 5581 [3, 5581] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5591 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 449 2347 5591 [5591] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5623 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 2579 5623 [5623] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5639 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 241 2579 5639 [5639] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5641 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 6679 5641 [3, 5641] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5647 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 2531 5647 [5647] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5651 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 619 2207 5651 [5651] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5653 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 7723 5653 [3, 5653] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5657 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 6823 5657 [3, 5657] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5659 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 563 2267 5659 [5659] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5669 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 997 7507 5669 [3, 5669] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5683 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 2339 5683 [5683] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5689 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 6871 5689 [3, 5689] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5693 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 7507 5693 [3, 5693] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5701 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 7699 5701 [3, 5701] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5711 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 389 2467 5711 [5711] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5717 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 7723 5717 [3, 5717] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5737 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 6823 5737 [3, 5737] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5741 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1021 7591 5741 [3, 5741] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5743 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 2579 5743 [5743] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5749 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 7963 5749 [3, 5749] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5779 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 683 2207 5779 [5779] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5783 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 313 2579 5783 [5783] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5791 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 317 2579 5791 [5791] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5801 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1831 6871 5801 [3, 5801] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5807 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 373 2531 5807 [5807] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5813 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 8059 5813 [3, 5813] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5821 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 7699 5821 [3, 5821] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5827 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 2411 5827 [5827] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5839 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 389 2531 5839 [5839] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5843 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 811 2111 5843 [5843] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow5849 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1951 6823 5849 [3, 5849] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5851 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 659 2267 5851 [5851] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

def lpfEntry10000WitnessLeaf9 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5227 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5231 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5233 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5237 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5261 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5273 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5279 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5281 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5297 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow5303 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5309 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5323 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5333 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5347 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5351 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5381 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5387 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5393 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5399 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow5407 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5413 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5417 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5419 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5431 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5437 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5441 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5443 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5449 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5471 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow5477 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5479 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5483 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5501 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5503 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5507 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5519 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5521 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5527 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow5531 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5557 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5563 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5569 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5573 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5581 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5591 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5623 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5639 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5641 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow5647 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5651 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5653 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5657 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5659 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5669 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5683 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5689 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5693 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow5701 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5711 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5717 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5737 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5741 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5743 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5749 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5779 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5783 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5791 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow5801 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5807 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5813 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5821 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5827 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow5839 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5843 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5849 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow5851 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
