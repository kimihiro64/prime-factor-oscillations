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

private def lpfEntry10000WitnessRow7229 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1201 9643 7229 [3, 7229] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7237 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1117 9739 7237 [3, 7237] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7243 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1091 2531 7243 [7243] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7247 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 2963 7247 [7247] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7253 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 997 9883 7253 [3, 7253] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7283 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1063 2579 7283 [7283] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7297 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 9283 7297 [3, 7297] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7307 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1123 2531 7307 [7307] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7309 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1321 9643 7309 [3, 7309] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7321 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2179 8803 7321 [3, 7321] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7331 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1087 2579 7331 [7331] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7333 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1117 9883 7333 [3, 7333] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7349 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1381 9643 7349 [3, 7349] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7351 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1097 2579 7351 [7351] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7369 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 8971 7369 [3, 7369] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7393 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1999 9091 7393 [3, 7393] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7411 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1367 2339 7411 [7411] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7417 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 9043 7417 [3, 7417] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7433 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 9067 7433 [3, 7433] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7451 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1259 2467 7451 [7451] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7457 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2143 9043 7457 [3, 7457] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7459 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1151 2579 7459 [7459] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7477 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1669 9547 7477 [3, 7477] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7481 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2179 9043 7481 [3, 7481] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7487 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3083 7487 [7487] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7489 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1951 9283 7489 [3, 7489] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7499 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1171 2579 7499 [7499] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7507 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1223 2531 7507 [7507] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7517 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1993 9283 7517 [3, 7517] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7523 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1231 2531 7523 [7523] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7529 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2203 9091 7529 [3, 7529] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7537 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1663 9643 7537 [3, 7537] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7541 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1429 9883 7541 [3, 7541] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7547 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1307 2467 7547 [7547] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7549 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1777 9547 7549 [3, 7549] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7559 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3119 7559 [7559] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7561 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2371 8971 7561 [3, 7561] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7573 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1621 9739 7573 [3, 7573] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7577 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 9283 7577 [3, 7577] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7583 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3019 7583 [7583] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7589 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1741 9643 7589 [3, 7589] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7591 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1217 2579 7591 [7591] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7603 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1223 2579 7603 [7603] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7607 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 877 2927 7607 [7607] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7621 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1549 9883 7621 [3, 7621] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7639 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 701 3119 7639 [7639] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7643 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1291 2531 7643 [7643] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7649 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1831 9643 7649 [3, 7649] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7669 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1621 9883 7669 [3, 7669] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7673 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2539 8971 7673 [3, 7673] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7681 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1783 9739 7681 [3, 7681] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7687 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 821 3023 7687 [7687] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7691 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1499 2347 7691 [7691] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7699 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1319 2531 7699 [7699] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7703 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3191 7703 [7703] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7717 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1693 9883 7717 [3, 7717] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7723 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1283 2579 7723 [7723] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7727 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3203 7727 [7727] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7741 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1873 9739 7741 [3, 7741] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7753 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 9547 7753 [3, 7753] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7757 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1753 9883 7757 [3, 7757] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7759 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 797 3083 7759 [7759] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7789 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1801 9883 7789 [3, 7789] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7793 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1951 9739 7793 [3, 7793] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7817 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2083 9643 7817 [3, 7817] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7823 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3251 7823 [7823] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7829 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1861 9883 7829 [3, 7829] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7841 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1879 9883 7841 [3, 7841] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7853 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2137 9643 7853 [3, 7853] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7867 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1523 2411 7867 [7867] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7873 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2719 9091 7873 [3, 7873] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7877 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1933 9883 7877 [3, 7877] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7879 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 773 3167 7879 [7879] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7883 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1531 2411 7883 [7883] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow7901 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 2113 9739 7901 [3, 7901] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow7907 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1423 2531 7907 [7907] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

def lpfEntry10000WitnessLeaf12 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7229 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7237 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7243 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7247 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow7253 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7283 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7297 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7307 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7309 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow7321 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7331 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7333 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7349 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7351 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow7369 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7393 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7411 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7417 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7433 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow7451 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7457 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7459 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7477 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7481 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow7487 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7489 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7499 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7507 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7517 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow7523 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7529 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7537 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7541 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7547 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow7549 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7559 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7561 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7573 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow7577 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7583 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7589 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7591 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7603 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow7607 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7621 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7639 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7643 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7649 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow7669 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7673 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7681 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7687 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7691 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow7699 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7703 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7717 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7723 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow7727 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7741 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7753 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7757 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7759 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow7789 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7793 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7817 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7823 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7829 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow7841 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7853 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7867 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7873 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7877 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow7879 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7883 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow7901 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow7907 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
