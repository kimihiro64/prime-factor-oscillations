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

private def lpfEntry10000WitnessRow401 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 103 499 401 [3, 401] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow409 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 151 463 409 [3, 409] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow419 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 43 167 419 [419] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow421 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 571 421 [3, 421] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow431 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 79 137 431 [431] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow433 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 103 547 433 [3, 433] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow439 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 53 167 439 [439] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow443 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 73 149 443 [443] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow449 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 103 571 449 [3, 449] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow457 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 227 2 457 [457] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow461 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 631 461 [3, 461] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow463 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 5 227 463 [463] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow467 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 97 137 467 [467] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow479 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 227 13 479 [479] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow487 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 107 137 487 [487] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow491 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 79 167 491 [491] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow499 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 23 227 499 [499] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow503 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 191 503 [503] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow509 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 157 607 509 [3, 509] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow521 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 151 631 521 [3, 521] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow523 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 131 131 523 [523] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow541 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 181 631 541 [3, 541] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow547 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 107 167 547 [547] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow557 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 109 727 557 [3, 557] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow563 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 199 563 [563] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow569 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 223 631 569 [3, 569] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow571 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 59 227 571 [571] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow577 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 367 499 577 [3, 577] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow587 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 127 167 587 [587] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow593 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 103 787 593 [3, 593] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow599 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 239 599 [599] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow601 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 271 631 601 [3, 601] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow607 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 137 167 607 [607] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow613 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 457 463 613 [3, 613] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow617 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 199 727 617 [3, 617] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow619 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 227 619 [619] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow631 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 89 227 631 [631] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow641 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 331 631 641 [3, 641] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow643 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 239 643 [643] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow647 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 97 227 647 [647] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow653 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 73 907 653 [3, 653] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow659 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 73 257 659 [659] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow661 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 241 751 661 [3, 661] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow673 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 103 907 673 [3, 673] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow677 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 109 907 677 [3, 677] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow683 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 281 683 [683] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow691 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 263 691 [691] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow701 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 859 701 [3, 701] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow709 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 157 907 709 [3, 709] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow719 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 277 719 [719] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow727 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 137 227 727 [727] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow733 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 907 733 [3, 733] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow739 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 113 257 739 [739] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow743 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 311 743 [743] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow751 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 113 263 751 [751] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow757 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 907 757 [3, 757] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow761 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 379 2 761 [761] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow769 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 367 787 769 [3, 769] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow773 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 967 773 [3, 773] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow787 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 5 167 227 787 [787] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow797 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 229 967 797 [3, 797] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow809 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 307 907 809 [3, 809] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow811 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 149 257 811 [811] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow821 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1039 821 [3, 821] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow823 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 101 311 823 [823] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow827 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 331 827 [827] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow829 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 337 907 829 [3, 829] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow839 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 359 839 [839] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow853 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1087 853 [3, 853] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow857 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 379 907 857 [3, 857] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow859 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 347 859 [859] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow863 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 73 359 863 [863] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow877 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1123 877 [3, 877] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow881 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 439 2 881 [881] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow883 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 83 359 883 [883] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow887 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 6 61 383 887 [887] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

def lpfEntry10000WitnessLeaf1 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow401 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow409 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow419 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow421 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow431 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow433 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow439 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow443 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow449 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow457 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow461 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow463 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow467 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow479 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow487 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow491 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow499 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow503 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow509 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow521 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow523 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow541 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow547 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow557 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow563 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow569 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow571 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow577 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow587 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow593 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow599 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow601 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow607 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow613 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow617 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow619 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow631 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow641 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow643 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow647 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow653 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow659 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow661 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow673 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow677 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow683 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow691 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow701 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow709 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow719 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow727 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow733 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow739 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow743 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow751 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow757 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow761 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow769 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow773 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow787 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow797 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow809 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow811 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow821 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow823 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow827 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow829 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow839 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow853 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow857 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow859 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow863 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow877 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow881 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow883 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow887 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
