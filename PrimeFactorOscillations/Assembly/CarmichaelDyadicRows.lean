/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelDyadicSpectrum

/-!
# Complete quadratic and quartic reference orders of the dyadic tree

All reference orders are evaluated in the actual finite atomic spectrum.
Missing children, terminal rows, the right-root exception and the nested
right-child collision are retained. The common weak rows are exactly the
nonterminal left nodes.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

theorem treeOrder_at_word (N : Nat) (H : Real) (hH : 0 < H)
    (b : Bool) (w : List Bool) :
    atomicOrder (treeSpectrum N H hH).point (treeSpectrum N H hH).mult
      (wordPoint H b w) =
        if w.length <= N then wordMultiplicity N w else 0 := by
  classical
  by_cases hw : w.length <= N
  . rw [ite_eq_left hw]
    have hp : (treeSpectrum N H hH).point (treeNode N b w hw) = wordPoint H b w := rfl
    rw [<- hp, atomicOrder_at _ _ (treeSpectrum N H hH).point_injective]
    rfl
  . rw [ite_eq_right hw]
    apply atomicOrder_zero
    intro i hi
    have he := @wordPoint_injective H (treeRaw i) (Prod.mk b w) hi
    have hew : i.2.val = w := congrArg (fun p : Prod Bool (List Bool) => p.2) he
    apply hw
    rw [<- hew]
    exact (mem_wordSupport N i.2.val).mp i.2.property

theorem tree_left_two_order (N : Nat) (H : Real) (hH : 0 < H)
    (w : List Bool) (hw : w.length <= N) :
    (treeSpectrum N H hH).rowOrder 2 (treeNode N false w hw) =
      if (false :: w).length <= N then wordMultiplicity N (false :: w) else 0 := by
  have hp : powerMap 2 ((treeSpectrum N H hH).point (treeNode N false w hw)) =
      wordPoint H true (false :: w) := by
    change (wordPoint H false w + 2 - 1) / 2 = _
    convert wordPoint_left_two H w using 1
    ring
  unfold ReflectedSpectrum.rowOrder
  rw [hp, treeOrder_at_word]

theorem tree_left_four_order (N : Nat) (H : Real) (hH : 0 < H)
    (w : List Bool) (hw : w.length <= N) :
    (treeSpectrum N H hH).rowOrder 4 (treeNode N false w hw) =
      if (true :: w).length <= N then wordMultiplicity N (true :: w) else 0 := by
  have hp : powerMap 4 ((treeSpectrum N H hH).point (treeNode N false w hw)) =
      wordPoint H true (true :: w) := by
    change (wordPoint H false w + 4 - 1) / 4 = _
    convert wordPoint_left_four H w using 1
    ring
  unfold ReflectedSpectrum.rowOrder
  rw [hp, treeOrder_at_word]

theorem tree_right_four_zero (N : Nat) (H : Real) (hH : 0 < H) (w : List Bool) :
    atomicOrder (treeSpectrum N H hH).point (treeSpectrum N H hH).mult
      (powerMap 4 (wordPoint H true w)) = 0 := by
  apply atomicOrder_zero
  intro i hi
  have h := powerMap_real_identity 4 (by norm_num) (wordPoint H true w)
  rw [<- hi] at h
  change ((treeSpectrum N H hH).point i).re * 4 = 1 - wordReal w + 4 - 1 at h
  have hu := (treeSpectrum_inner_strip N H hH i).2
  have hx := (wordReal_bounds w).2
  linarith

theorem tree_right_two_zero_of_re (N : Nat) (H : Real) (hH : 0 < H)
    (w : List Bool) (hx : wordReal w < 2 / 7) :
    atomicOrder (treeSpectrum N H hH).point (treeSpectrum N H hH).mult
      (powerMap 2 (wordPoint H true w)) = 0 := by
  apply atomicOrder_zero
  intro i hi
  have h := powerMap_real_identity 2 (by norm_num) (wordPoint H true w)
  rw [<- hi] at h
  change ((treeSpectrum N H hH).point i).re * 2 = 1 - wordReal w + 2 - 1 at h
  have hu := (treeSpectrum_inner_strip N H hH i).2
  linarith

theorem tree_right_two_order (N : Nat) (H : Real) (hH : 0 < H)
    (w : List Bool) (hw : w.length <= N) :
    (treeSpectrum N H hH).rowOrder 2 (treeNode N true w hw) =
      match w with
      | [] => 0
      | false :: v => wordMultiplicity N (true :: v)
      | true :: _ => 0 := by
  cases w with
  | nil =>
    exact tree_right_two_zero_of_re N H hH [] (by norm_num [wordReal])
  | cons b w =>
    cases b
    . have hp : powerMap 2 (wordPoint H true (false :: w)) =
          wordPoint H true (true :: w) := by
        change (wordPoint H true (false :: w) + 2 - 1) / 2 = _
        convert wordPoint_right_false_two H w using 1
        ring
      change atomicOrder _ _ (powerMap 2 (wordPoint H true (false :: w))) = _
      have ht : (true :: w).length <= N := by simpa only [List.length_cons] using hw
      rw [hp, treeOrder_at_word, ite_eq_left ht]
    . apply tree_right_two_zero_of_re N H hH (true :: w)
      have h := (wordReal_true_bounds w).2
      linarith

theorem tree_left_weak_iff (N : Nat) (H : Real) (hH : 0 < H)
    (w : List Bool) (hw : w.length <= N) :
    Membership.mem (treeSpectrum N H hH).weakIndices (treeNode N false w hw) <->
      w.length < N := by
  classical
  rw [ReflectedSpectrum.weakIndices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change ((wordMultiplicity N w : Real) <=
      2 * ((treeSpectrum N H hH).rowOrder 2 (treeNode N false w hw) : Real) /\
    (wordMultiplicity N w : Real) <=
      4 * ((treeSpectrum N H hH).rowOrder 4 (treeNode N false w hw) : Real)) <-> _
  rw [tree_left_two_order, tree_left_four_order]
  by_cases hi : w.length < N
  . have hc : (false :: w).length <= N := by simp only [List.length_cons]; omega
    have ht : (true :: w).length <= N := by simpa only [List.length_cons] using hc
    rw [ite_eq_left hc, ite_eq_left ht]
    have h2 : (wordMultiplicity N w : Real) =
        2 * (wordMultiplicity N (false :: w) : Real) := by
      exact_mod_cast wordMultiplicity_false N w hi
    have h4 : (wordMultiplicity N w : Real) =
        4 * (wordMultiplicity N (true :: w) : Real) := by
      exact_mod_cast wordMultiplicity_true N w hi
    constructor
    . intro h
      exact hi
    . intro h
      constructor <;> linarith
  . have hc : Not ((false :: w).length <= N) := by simp only [List.length_cons]; omega
    have ht : Not ((true :: w).length <= N) := by simpa only [List.length_cons] using hc
    rw [ite_eq_right hc, ite_eq_right ht]
    have hp : (0 : Real) < (wordMultiplicity N w : Real) := by
      exact_mod_cast wordMultiplicity_pos N w
    constructor
    . intro h
      have hh := h.1
      simp only [Nat.cast_zero, mul_zero] at hh
      exact False.elim ((not_le_of_gt hp) hh)
    . intro h
      exact False.elim (hi h)

theorem tree_right_not_weak (N : Nat) (H : Real) (hH : 0 < H)
    (w : List Bool) (hw : w.length <= N) :
    Not (Membership.mem (treeSpectrum N H hH).weakIndices (treeNode N true w hw)) := by
  classical
  intro hi
  have h := (Finset.mem_filter.mp hi).2.2
  change (wordMultiplicity N w : Real) <= 4 *
    (atomicOrder (treeSpectrum N H hH).point (treeSpectrum N H hH).mult
      (powerMap 4 (wordPoint H true w)) : Real) at h
  rw [tree_right_four_zero] at h
  have hp : (0 : Real) < (wordMultiplicity N w : Real) := by
    exact_mod_cast wordMultiplicity_pos N w
  simp only [Nat.cast_zero, mul_zero] at h
  exact (not_le_of_gt hp) h

theorem tree_weak_iff (N : Nat) (H : Real) (hH : 0 < H) (i : TreeIndex N) :
    Membership.mem (treeSpectrum N H hH).weakIndices i <->
      i.1 = false /\ i.2.val.length < N := by
  cases i with
  | mk b w =>
    cases w with
    | mk w hw =>
      have hLen := (mem_wordSupport N w).mp hw
      cases b
      . simpa [treeNode] using tree_left_weak_iff N H hH w hLen
      . simpa [treeNode] using tree_right_not_weak N H hH w hLen

end PrimeFactorOscillations.CarmichaelDyadicSharpness
