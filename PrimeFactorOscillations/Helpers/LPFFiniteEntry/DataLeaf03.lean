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

private def lpfEntry10000WitnessRow1471 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 149 587 1471 [1471] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1481 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 643 1579 1481 [3, 1481] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1483 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 251 491 1483 [1483] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1487 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 113 631 1487 [1487] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1489 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 691 1543 1489 [3, 1489] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1493 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 2011 1493 [3, 1493] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1499 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 103 647 1499 [1499] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1511 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 109 647 1511 [1511] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1523 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 191 571 1523 [1523] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1531 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 179 587 1531 [1531] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1543 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 281 491 1543 [1543] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1549 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 2131 1549 [3, 1549] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1553 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 751 1579 1553 [3, 1553] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1559 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 149 631 1559 [1559] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1567 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 197 587 1567 [1567] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1571 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 179 607 1571 [1571] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1579 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 311 479 1579 [1579] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1583 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 787 5 1583 [1583] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1597 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 409 1987 1597 [3, 1597] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1601 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 823 1579 1601 [3, 1601] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1607 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 157 647 1607 [1607] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1609 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 691 1723 1609 [3, 1609] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1613 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 409 2011 1613 [3, 1613] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1619 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 727 1619 [1619] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1621 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 421 2011 1621 [3, 1621] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1627 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 347 467 1627 [1627] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1637 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 709 1747 1637 [3, 1637] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1657 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 619 1867 1657 [3, 1657] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1663 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 659 1663 [1663] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1667 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 263 571 1667 [1667] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1669 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 373 2131 1669 [3, 1669] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1693 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 2347 1693 [3, 1693] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1697 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 823 1723 1697 [3, 1697] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1699 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 263 587 1699 [1699] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1709 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 313 2251 1709 [3, 1709] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1721 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 859 2 1721 [1721] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1723 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 383 479 1723 [1723] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1733 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 349 2251 1733 [3, 1733] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1741 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 601 2011 1741 [3, 1741] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1747 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 383 491 1747 [1747] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1753 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 619 2011 1753 [3, 1753] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1759 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 647 1759 [1759] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1777 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 887 2 1777 [1777] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1783 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 719 1783 [1783] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1787 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 263 631 1787 [1787] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1789 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 433 2251 1789 [3, 1789] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1801 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 691 2011 1801 [3, 1801] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1811 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 179 727 1811 [1811] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1823 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 281 631 1823 [1823] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1831 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 743 1831 [1831] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1847 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 197 727 1847 [1847] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1861 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 541 2251 1861 [3, 1861] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1867 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 347 587 1867 [1867] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1871 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 149 787 1871 [1871] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1873 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 823 1987 1873 [3, 1873] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1877 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 349 2467 1877 [3, 1877] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1879 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 647 1879 [1879] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1889 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 823 2011 1889 [3, 1889] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1901 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 601 2251 1901 [3, 1901] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1907 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 307 647 1907 [1907] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1913 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 619 2251 1913 [3, 1913] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1931 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 179 787 1931 [1931] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1933 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 433 2467 1933 [3, 1933] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1949 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 577 2347 1949 [3, 1949] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1951 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 743 1951 [1951] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1973 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 613 2347 1973 [3, 1973] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1979 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 907 1979 [1979] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1987 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 347 647 1987 [1987] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow1993 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 643 2347 1993 [3, 1993] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1997 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1009 1987 1997 [3, 1997] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow1999 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 827 1999 [1999] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2003 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 431 571 2003 [2003] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2011 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 359 647 2011 [2011] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2017 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1039 1987 2017 [3, 2017] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2027 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 367 647 2027 [2027] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2029 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 577 2467 2029 [3, 2029] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

def lpfEntry10000WitnessLeaf3 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1471 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1481 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1483 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1487 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1489 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1493 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1499 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1511 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1523 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow1531 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1543 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1549 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1553 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1559 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1567 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1571 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1579 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1583 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1597 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow1601 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1607 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1609 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1613 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1619 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1621 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1627 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1637 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1657 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1663 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow1667 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1669 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1693 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1697 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1699 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1709 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1721 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1723 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1733 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow1741 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1747 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1753 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1759 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1777 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1783 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1787 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1789 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1801 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1811 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow1823 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1831 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1847 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1861 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1867 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1871 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1873 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1877 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1879 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow1889 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1901 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1907 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1913 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1931 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow1933 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1949 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1951 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1973 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1979 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow1987 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow1993 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1997 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow1999 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2003 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2011 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2017 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2027 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2029 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
