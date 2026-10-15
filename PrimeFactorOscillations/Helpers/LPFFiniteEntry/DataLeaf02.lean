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

private def lpfEntry10000WitnessRow911 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 73 383 911 [911] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow919 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 101 359 919 [919] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow929 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 463 2 929 [929] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow937 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 467 2 937 [937] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow941 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 241 1171 941 [3, 941] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow947 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 163 311 947 [947] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow953 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 523 907 953 [3, 953] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow967 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 101 383 967 [967] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow971 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 103 383 971 [971] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow977 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 487 2 977 [977] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow983 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 431 983 [983] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow991 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 113 383 991 [991] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow997 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1303 997 [3, 997] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1009 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 607 907 1009 [3, 1009] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1013 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1327 1013 [3, 1013] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1019 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 151 359 1019 [1019] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1021 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 1303 1021 [3, 1021] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1031 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 149 367 1031 [1031] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1033 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 421 1129 1033 [3, 1033] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1039 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 101 419 1039 [1039] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1049 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 523 2 1049 [1049] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1051 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 179 347 1051 [1051] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1061 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1399 1061 [3, 1061] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1063 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 101 431 1063 [1063] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1069 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 313 1291 1069 [3, 1069] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1087 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 113 431 1087 [1087] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1091 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 463 1091 [1091] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1093 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1447 1093 [3, 1093] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1097 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 547 2 1097 [1097] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1103 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 491 1103 [1103] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1109 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1471 1109 [3, 1109] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1117 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1483 1117 [3, 1117] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1123 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 479 1123 [1123] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1129 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 787 907 1129 [3, 1129] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1151 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 109 467 1151 [1151] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1153 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 433 1297 1153 [3, 1153] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1163 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 499 1163 [1163] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1171 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 239 347 1171 [1171] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1181 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1579 1181 [3, 1181] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1187 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 103 491 1187 [1187] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1193 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 619 1171 1193 [3, 1193] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1201 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 599 2 1201 [1201] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1213 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1627 1213 [3, 1213] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1217 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 607 2 1217 [1217] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1223 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 113 499 1223 [1223] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1229 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 313 1531 1229 [3, 1229] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1231 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 149 467 1231 [1231] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1237 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 1627 1237 [3, 1237] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1249 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 577 1297 1249 [3, 1249] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1259 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 547 1259 [1259] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1277 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1723 1277 [3, 1277] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1279 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 149 491 1279 [1279] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1283 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 151 491 1283 [1283] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1289 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 643 2 1289 [1289] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1291 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 179 467 1291 [1291] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1297 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 647 2 1297 [1297] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1301 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 1723 1301 [3, 1301] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1303 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 647 5 1303 [1303] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1307 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 571 1307 [1307] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1319 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 73 587 1319 [1319] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1321 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 659 2 1321 [1321] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1327 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 197 467 1327 [1327] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1361 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 619 1423 1361 [3, 1361] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1367 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 113 571 1367 [1367] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1373 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1867 1373 [3, 1373] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1381 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 349 1723 1381 [3, 1381] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1399 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 113 587 1399 [1399] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1409 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 643 1471 1409 [3, 1409] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1423 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 281 431 1423 [1423] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1427 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 631 1427 [1427] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1429 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 397 1747 1429 [3, 1429] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1433 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 619 1531 1433 [3, 1433] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1439 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 73 647 1439 [1439] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1447 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 257 467 1447 [1447] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1451 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 179 547 1451 [1451] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1453 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1987 1453 [3, 1453] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

def lpfEntry10000WitnessLeaf2 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow911 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow919 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow929 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow937 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow941 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow947 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow953 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow967 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow971 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow977 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow983 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow991 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow997 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1009 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1013 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1019 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1021 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1031 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1033 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow1039 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1049 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1051 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1061 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1063 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1069 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1087 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1091 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1093 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1097 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow1103 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1109 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1117 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1123 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1129 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1151 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1153 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1163 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1171 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow1181 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1187 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1193 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1201 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1213 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1217 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1223 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1229 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1231 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1237 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow1249 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1259 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1277 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1279 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1283 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1289 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1291 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1297 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1301 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow1303 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1307 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1319 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1321 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1327 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1361 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1367 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1373 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1381 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1399 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow1409 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1423 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1427 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1429 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1433 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1439 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1447 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1451 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1453 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
