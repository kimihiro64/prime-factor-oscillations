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

private def lpfEntry10000WitnessRow3 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 2 7 7 3 [3, 3, 3] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow5 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 11 2 5 [5, 5] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 1 2 2 7 [7] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow11 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 3 3 3 11 [11] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow13 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 3 3 17 13 [3, 13] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow17 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 2 7 2 17 [17] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow19 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 3 3 7 19 [19] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow23 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 11 47 23 [5, 23] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow29 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 13 2 29 [29] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow31 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 11 67 31 [5, 31] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow37 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 3 17 2 37 [37] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow41 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 19 2 41 [41] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow43 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 11 11 43 [43] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow47 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 3 17 7 47 [47] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow53 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 13 67 53 [3, 53] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow59 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 11 19 59 [59] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow61 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 29 2 61 [61] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow67 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 3 17 17 67 [67] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow71 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 19 17 71 [71] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow73 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 29 227 73 [7, 73] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow79 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 37 3 79 [79] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow83 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 5 37 83 [83] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow89 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 67 67 89 [3, 89] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow97 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 47 2 97 [97] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow101 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 127 227 101 [7, 101] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow103 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 5 47 103 [103] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow107 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 37 17 107 [107] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow109 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 53 2 109 [109] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow113 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 31 139 113 [3, 113] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow127 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 47 17 127 [127] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow131 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 19 47 131 [131] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow137 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 67 2 137 [137] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow139 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 67 3 139 [139] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow149 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 97 127 149 [3, 149] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow151 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 5 71 151 [151] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow157 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 97 139 157 [3, 157] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow163 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 23 59 163 [163] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow167 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 37 47 167 [167] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow173 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 199 173 [3, 173] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow179 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 23 67 179 [179] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow181 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 89 2 181 [181] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow191 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 29 67 191 [191] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow193 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 109 181 193 [3, 193] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow197 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 97 2 197 [197] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow199 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 29 71 199 [199] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow211 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 53 53 211 [211] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow223 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 5 107 223 [223] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow227 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 4 47 67 227 [227] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow229 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 283 229 [3, 229] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow233 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 73 277 233 [3, 233] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow239 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 23 97 239 [239] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow241 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 151 211 241 [3, 241] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow251 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 29 97 251 [251] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow257 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 127 2 257 [257] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow263 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 5 127 263 [263] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow269 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 73 331 269 [3, 269] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow271 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 5 131 271 [271] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow277 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 137 2 277 [277] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow281 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 139 2 281 [281] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow283 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 5 137 283 [283] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow293 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 379 293 [3, 293] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow307 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 23 131 307 [307] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow311 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 29 127 311 [311] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow313 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 103 367 313 [3, 313] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow317 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 109 367 317 [3, 317] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow331 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 29 137 331 [331] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow337 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 167 2 337 [337] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow347 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 43 131 347 [347] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow349 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 463 349 [3, 349] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow353 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 73 457 353 [3, 353] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow359 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 41 139 359 [359] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow367 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 53 131 367 [367] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow373 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 499 373 [3, 373] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow379 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 23 167 379 [379] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow383 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 53 139 383 [383] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow389 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 523 389 [3, 389] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

def lpfEntry10000WitnessLeaf0 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow5 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow11 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow13 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow17 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow19 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow23 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow29 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow31 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow37 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow41 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow43 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow47 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow53 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow59 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow61 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow67 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow71 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow73 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow79 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow83 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow89 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow97 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow101 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow103 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow107 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow109 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow113 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow127 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow131 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow137 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow139 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow149 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow151 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow157 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow163 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow167 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow173 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow179 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow181 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow191 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow193 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow197 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow199 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow211 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow223 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow227 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow229 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow233 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow239 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow241 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow251 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow257 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow263 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow269 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow271 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow277 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow281 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow283 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow293 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow307 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow311 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow313 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow317 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow331 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow337 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow347 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow349 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow353 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow359 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow367 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow373 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow379 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow383 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow389 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
