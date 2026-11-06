/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelDyadicRows
import PrimeFactorOscillations.Assembly.CarmichaelSimpleTreeSpectrum

/-!
# Exact common-weak support of the simple dyadic spectrum

All left reference orders are evaluated in the actual finite atomic model.
Terminal children are absent, and the right quartic reference is absent.
The right quadratic row remains in the full readout; it cannot change the
union carrier because every right point has a negative quartic projection.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

theorem simpleTreeOrder_at_word (N : Nat) (H : Real) (hH : 0 < H)
    (b : Bool) (w : List Bool) :
    atomicOrder (simpleTreeSpectrum N H hH).point (simpleTreeSpectrum N H hH).mult
      (wordPoint H b w) = if w.length <= N then 1 else 0 := by
  classical
  by_cases hw : w.length <= N
  . rw [ite_eq_left hw]
    have hp : (simpleTreeSpectrum N H hH).point (treeNode N b w hw) =
        wordPoint H b w := rfl
    rw [<- hp, atomicOrder_at _ _ (simpleTreeSpectrum N H hH).point_injective]
    rfl
  . rw [ite_eq_right hw]
    apply atomicOrder_zero
    intro i hi
    have he := @wordPoint_injective H (treeRaw i) (Prod.mk b w) hi
    have hew : i.2.val = w := congrArg (fun p : Prod Bool (List Bool) => p.2) he
    apply hw
    rw [<- hew]
    exact (mem_wordSupport N i.2.val).mp i.2.property

theorem simpleTree_left_two_order (N : Nat) (H : Real) (hH : 0 < H)
    (w : List Bool) (hw : w.length <= N) :
    (simpleTreeSpectrum N H hH).rowOrder 2 (treeNode N false w hw) =
      if (false :: w).length <= N then 1 else 0 := by
  have hp : powerMap 2 ((simpleTreeSpectrum N H hH).point (treeNode N false w hw)) =
      wordPoint H true (false :: w) := by
    change (wordPoint H false w + 2 - 1) / 2 = _
    convert wordPoint_left_two H w using 1
    ring
  unfold ReflectedSpectrum.rowOrder
  rw [hp, simpleTreeOrder_at_word]

theorem simpleTree_left_four_order (N : Nat) (H : Real) (hH : 0 < H)
    (w : List Bool) (hw : w.length <= N) :
    (simpleTreeSpectrum N H hH).rowOrder 4 (treeNode N false w hw) =
      if (true :: w).length <= N then 1 else 0 := by
  have hp : powerMap 4 ((simpleTreeSpectrum N H hH).point (treeNode N false w hw)) =
      wordPoint H true (true :: w) := by
    change (wordPoint H false w + 4 - 1) / 4 = _
    convert wordPoint_left_four H w using 1
    ring
  unfold ReflectedSpectrum.rowOrder
  rw [hp, simpleTreeOrder_at_word]

theorem simpleTree_right_four_zero (N : Nat) (H : Real) (hH : 0 < H)
    (w : List Bool) :
    atomicOrder (simpleTreeSpectrum N H hH).point (simpleTreeSpectrum N H hH).mult
      (powerMap 4 (wordPoint H true w)) = 0 := by
  apply atomicOrder_zero
  intro i hi
  have hp : (treeSpectrum N H hH).point i = powerMap 4 (wordPoint H true w) := hi
  have h := tree_right_four_zero N H hH w
  rw [<- hp, atomicOrder_at _ _ (treeSpectrum N H hH).point_injective] at h
  exact (Nat.ne_of_gt ((treeSpectrum N H hH).mult_pos i)) h

theorem simpleTree_left_weak_iff (N : Nat) (H : Real) (hH : 0 < H)
    (w : List Bool) (hw : w.length <= N) :
    Membership.mem (simpleTreeSpectrum N H hH).weakIndices (treeNode N false w hw) <->
      w.length < N := by
  classical
  rw [ReflectedSpectrum.weakIndices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change (((1 : Nat) : Real) <=
      2 * ((simpleTreeSpectrum N H hH).rowOrder 2 (treeNode N false w hw) : Real) /\
    ((1 : Nat) : Real) <=
      4 * ((simpleTreeSpectrum N H hH).rowOrder 4 (treeNode N false w hw) : Real)) <-> _
  rw [simpleTree_left_two_order, simpleTree_left_four_order]
  by_cases hi : w.length < N
  . have hc : (false :: w).length <= N := by simp only [List.length_cons]; omega
    have ht : (true :: w).length <= N := by simpa only [List.length_cons] using hc
    rw [ite_eq_left hc, ite_eq_left ht]
    norm_num [hi]
  . have hc : Not ((false :: w).length <= N) := by simp only [List.length_cons]; omega
    have ht : Not ((true :: w).length <= N) := by simpa only [List.length_cons] using hc
    rw [ite_eq_right hc, ite_eq_right ht]
    norm_num [hi]

theorem simpleTree_right_not_weak (N : Nat) (H : Real) (hH : 0 < H)
    (w : List Bool) (hw : w.length <= N) :
    Not (Membership.mem (simpleTreeSpectrum N H hH).weakIndices (treeNode N true w hw)) := by
  classical
  intro hi
  have h := (Finset.mem_filter.mp hi).2.2
  change ((1 : Nat) : Real) <= 4 *
    (atomicOrder (simpleTreeSpectrum N H hH).point (simpleTreeSpectrum N H hH).mult
      (powerMap 4 (wordPoint H true w)) : Real) at h
  rw [simpleTree_right_four_zero] at h
  norm_num at h

theorem simpleTree_weak_iff (N : Nat) (H : Real) (hH : 0 < H) (i : TreeIndex N) :
    Membership.mem (simpleTreeSpectrum N H hH).weakIndices i <->
      i.1 = false /\ i.2.val.length < N := by
  cases i with
  | mk b w =>
    cases w with
    | mk w hw =>
      have hLen := (mem_wordSupport N w).mp hw
      cases b
      . simpa [treeNode] using simpleTree_left_weak_iff N H hH w hLen
      . simpa [treeNode] using simpleTree_right_not_weak N H hH w hLen

end PrimeFactorOscillations.CarmichaelDyadicSharpness
