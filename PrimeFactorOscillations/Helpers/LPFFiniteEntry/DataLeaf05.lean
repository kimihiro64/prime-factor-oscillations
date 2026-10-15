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

private def lpfEntry10000WitnessRow2671 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1163 2671 [2671] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2677 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 3259 2677 [3, 2677] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2683 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 1049 2683 [2683] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2687 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1171 2687 [2687] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2689 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1567 2467 2689 [3, 2689] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2693 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 3307 2693 [3, 2693] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2699 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 373 977 2699 [2699] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2707 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 401 953 2707 [2707] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2711 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1163 2711 [2711] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2713 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1723 2347 2713 [3, 2713] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2719 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1187 2719 [2719] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2729 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1627 2467 2729 [3, 2729] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2731 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 269 1097 2731 [2731] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2741 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 3259 2741 [3, 2741] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2749 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3463 2749 [3, 2749] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2753 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1193 8443 2753 [7, 2753] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2767 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 233 1151 2767 [2767] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2777 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1699 2467 2777 [3, 2777] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2789 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 3331 2789 [3, 2789] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2791 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1223 2791 [2791] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2797 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 3463 2797 [3, 2797] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2801 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1399 2 2801 [2801] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2803 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 353 1049 2803 [2803] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2819 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1217 2819 [2819] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2833 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1033 3217 2833 [3, 2833] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2837 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 757 3499 2837 [3, 2837] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2843 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 1129 2843 [2843] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2851 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 983 2851 [2851] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2857 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1427 2 2857 [2857] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2861 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3631 2861 [3, 2861] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2879 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 269 1171 2879 [2879] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2887 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 1151 2887 [2887] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2897 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1447 2 2897 [2897] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2903 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1279 2903 [2903] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2909 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 3631 2909 [3, 2909] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2917 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 3643 2917 [3, 2917] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2927 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1291 2927 [2927] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2939 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1297 2939 [2939] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2953 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 3697 2953 [3, 2953] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2957 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 853 3583 2957 [3, 2957] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow2963 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 353 1129 2963 [2963] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2969 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1483 2 2969 [2969] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2971 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 269 1217 2971 [2971] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow2999 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1327 2999 [2999] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3001 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1499 2 3001 [3001] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3011 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 409 1097 3011 [3011] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3019 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 1217 3019 [3019] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3023 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1319 3023 [3023] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3037 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 3823 3037 [3, 3037] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3041 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 1321 9323 3041 [7, 3041] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3049 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1523 2 3049 [3049] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3061 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 3931 3061 [3, 3061] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3067 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 317 1217 3067 [3067] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3079 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1367 3079 [3079] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3083 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 503 1039 3083 [3083] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3089 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1543 2 3089 [3089] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3109 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4003 3109 [3, 3109] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3119 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 193 1367 3119 [3119] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3121 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1559 2 3121 [3121] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3137 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1567 2 3137 [3137] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3163 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 563 1019 3163 [3163] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3167 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 293 1291 3167 [3167] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3169 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1583 2 3169 [3169] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3181 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4111 3181 [3, 3181] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3187 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1151 3187 [3187] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3191 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 173 1423 3191 [3191] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3203 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 563 1039 3203 [3203] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3209 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 2347 2467 3209 [3, 3209] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3217 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1607 2 3217 [3217] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3221 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 4099 3221 [3, 3221] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3229 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 733 4111 3229 [3, 3229] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3251 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 409 1217 3251 [3251] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3253 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 8 661 4219 3253 [3, 3253] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)

private def lpfEntry10000WitnessRow3257 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 1627 2 3257 [3257] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3259 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 443 1187 3259 [3259] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

private def lpfEntry10000WitnessRow3271 : TreeOrbitWitness :=
  TreeOrbitWitness.mk 7 269 1367 3271 [3271] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)

def lpfEntry10000WitnessLeaf5 : OrbitWitnessTree :=
  (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2671 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2677 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2683 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2687 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2689 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2693 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2699 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2707 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2711 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow2713 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2719 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2729 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2731 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2741 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2749 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2753 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2767 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2777 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2789 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow2791 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2797 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2801 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2803 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2819 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2833 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2837 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2843 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2851 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2857 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow2861 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2879 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2887 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2897 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2903 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2909 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2917 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2927 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2939 OrbitWitnessTree.empty)))))
  lpfEntry10000WitnessRow2953 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2957 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2963 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow2969 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow2971 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow2999 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3001 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3011 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3019 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3023 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow3037 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3041 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3049 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3061 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3067 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3079 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3083 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3089 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3109 OrbitWitnessTree.empty))))
  lpfEntry10000WitnessRow3119 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3121 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3137 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3163 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3167 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3169 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3181 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3187 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3191 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3203 OrbitWitnessTree.empty)))
  lpfEntry10000WitnessRow3209 (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3217 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3221 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3229 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3251 OrbitWitnessTree.empty))
  lpfEntry10000WitnessRow3253 (OrbitWitnessTree.node (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3257 OrbitWitnessTree.empty)
  lpfEntry10000WitnessRow3259 (OrbitWitnessTree.node OrbitWitnessTree.empty
  lpfEntry10000WitnessRow3271 OrbitWitnessTree.empty))))))

end PrimeFactorOscillations.LPF
