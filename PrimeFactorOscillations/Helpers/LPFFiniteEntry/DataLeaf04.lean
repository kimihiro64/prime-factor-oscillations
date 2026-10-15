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

private def lpfEntry10000WitnessRow2053 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 613 2467 2053 [3, 2053] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2063 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 859 2063 [2063] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2069 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 2371 2069 [3, 2069] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2081 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 991 2131 2081 [3, 2081] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2083 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 809 2083 [2083] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2087 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 257 787 2087 [2087] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2089 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 883 2251 2089 [3, 2089] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2099 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 263 787 2099 [2099] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2111 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 149 907 2111 [2111] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2113 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 823 2347 2113 [3, 2113] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2129 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1063 2 2129 [2129] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2131 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 419 647 2131 [2131] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2137 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 739 2467 2137 [3, 2137] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2141 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 2551 2141 [3, 2141] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2143 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 839 2143 [2143] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2153 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 883 2347 2153 [3, 2153] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2161 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 991 2251 2161 [3, 2161] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2179 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 857 2179 [2179] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2203 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 929 2203 [2203] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2207 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 197 907 2207 [2207] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2213 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 2659 2213 [3, 2213] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2221 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 2671 2221 [3, 2221] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2237 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1009 2347 2237 [3, 2237] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2239 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 947 2239 [2239] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2243 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 491 631 2243 [2243] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2251 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 479 647 2251 [2251] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2267 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 347 787 2267 [2267] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2269 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 937 2467 2269 [3, 2269] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2273 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1063 2347 2273 [3, 2273] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2281 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1171 2251 2281 [3, 2281] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2287 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 971 2287 [2287] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2293 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 2707 2293 [3, 2293] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2297 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1459 1987 2297 [3, 2297] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2309 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 2803 2309 [3, 2309] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2311 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 983 2311 [2311] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2333 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 2767 2333 [3, 2333] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2339 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 263 907 2339 [2339] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2341 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 2851 2341 [3, 2341] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2347 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 587 587 2347 [2347] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2351 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 983 2351 [2351] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2357 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 2803 2357 [3, 2357] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2371 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 953 2371 [2371] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2377 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1187 2 2377 [2377] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2381 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 2719 2381 [3, 2381] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2383 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1019 2383 [2383] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2389 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 2851 2389 [3, 2389] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2393 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1123 2467 2393 [3, 2393] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2399 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 971 2399 [2399] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2411 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 419 787 2411 [2411] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2417 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1279 2347 2417 [3, 2417] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2423 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1039 2423 [2423] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2437 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1217 2 2437 [2437] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2441 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1531 2131 2441 [3, 2441] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2447 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1051 2447 [2447] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2459 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 937 2459 [2459] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2467 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 587 647 2467 [2467] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2473 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1459 2251 2473 [3, 2473] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2477 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 997 2719 2477 [3, 2477] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2503 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 1019 2503 [2503] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2521 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1259 2 2521 [2521] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2531 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 359 907 2531 [2531] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2539 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1097 2539 [2539] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2543 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 1039 2543 [2543] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2549 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3163 2549 [3, 2549] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2551 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1103 2551 [2551] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2557 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 3079 2557 [3, 2557] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2579 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 383 907 2579 [2579] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2591 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1123 2591 [2591] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2593 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1423 2467 2593 [3, 2593] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2609 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1303 2 2609 [2609] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2617 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1307 2 2617 [2617] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2621 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3271 2621 [3, 2621] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2633 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1483 2467 2633 [3, 2633] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2647 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1151 2647 [2647] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2657 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1327 2 2657 [2657] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2659 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 1097 2659 [2659] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

def lpfEntry10000WitnessLeaf4 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2053 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2063 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2069 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2081 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2083 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2087 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2089 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2099 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2111 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow2113 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2129 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2131 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2137 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2141 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2143 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2153 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2161 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2179 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2203 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow2207 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2213 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2221 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2237 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2239 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2243 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2251 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2267 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2269 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2273 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow2281 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2287 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2293 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2297 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2309 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2311 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2333 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2339 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2341 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow2347 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2351 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2357 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2371 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2377 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2381 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2383 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2389 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2393 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2399 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow2411 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2417 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2423 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2437 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2441 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2447 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2459 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2467 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2473 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow2477 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2503 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2521 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2531 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2539 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2543 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2549 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2551 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2557 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2579 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow2591 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2593 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2609 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2617 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2621 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2633 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2647 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2657 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2659 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
