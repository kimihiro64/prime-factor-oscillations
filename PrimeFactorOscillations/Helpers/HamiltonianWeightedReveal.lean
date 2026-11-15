/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.NormNum

/-! # A weighted sequential-reveal subprobability

This is the probabilistic input to the row-cap permanent bound used
for the large-minor tail. Every matching keeps its own available-column
denominator. The finite family is separated only by its full row history.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {R C L : Type*} [DecidableEq C] [DecidableEq L]

def hamiltonianRevealWeight (A : R -> C -> Real) :
    List R -> Finset C -> (R -> C) -> Real
  | [], _, _ => 1
  | i :: rows, available, f =>
      A i (f i) / available.sum (A i) *
        hamiltonianRevealWeight A rows (available.erase (f i)) f

theorem hamiltonian_reveal_weight_nonnegative (A : R -> C -> Real)
    (hA : forall i j, 0 <= A i j) (rows : List R) (available : Finset C) (f : R -> C) :
    0 <= hamiltonianRevealWeight A rows available f := by
  induction rows generalizing available with
  | nil => norm_num [hamiltonianRevealWeight]
  | cons i rows ih =>
    exact mul_nonneg (div_nonneg (hA i (f i)) (Finset.sum_nonneg (fun j _ => hA i j)))
      (ih (available.erase (f i)))

theorem hamiltonian_reveal_family_subprobability
    (A : R -> C -> Real) (hA : forall i j, 0 <= A i j)
    (rows : List R) (available : Finset C) (s : Finset L) (f : L -> R -> C)
    (hMap : forall z, Membership.mem s z -> forall i, Membership.mem rows i ->
      Membership.mem available (f z i))
    (hDistinct : forall z, Membership.mem s z ->
      List.Pairwise (fun i j => Not (f z i = f z j)) rows)
    (hSeparate : forall z, Membership.mem s z -> forall w, Membership.mem s w ->
      (forall i, Membership.mem rows i -> f z i = f w i) -> z = w) :
    s.sum (fun z => hamiltonianRevealWeight A rows available (f z)) <= 1 := by
  induction rows generalizing available s with
  | nil =>
    have hCard : s.card <= 1 := Finset.card_le_one.mpr (fun z hz w hw =>
      hSeparate z hz w hw (fun i hi => False.elim (List.not_mem_nil hi)))
    have hCast : (s.card : Real) <= 1 := by exact_mod_cast hCard
    simpa only [hamiltonianRevealWeight, Finset.sum_const, nsmul_eq_mul, mul_one] using hCast
  | cons i rows ih =>
    let total := available.sum (A i)
    have hTotal : 0 <= total := Finset.sum_nonneg (fun j _ => hA i j)
    have hBranch (j : C) :
        (s.filter (fun z => f z i = j)).sum
          (fun z => hamiltonianRevealWeight A rows (available.erase j) (f z)) <= 1 := by
      apply ih
      case hMap =>
        intro z hz k hk
        have hzS := (Finset.mem_filter.mp hz).1
        have hzJ := (Finset.mem_filter.mp hz).2
        have hUnequal := (List.pairwise_cons.mp (hDistinct z hzS)).1 k hk
        exact Finset.mem_erase.mpr (And.intro
          (fun hEq => hUnequal (hzJ.trans hEq.symm))
          (hMap z hzS k (List.mem_cons_of_mem i hk)))
      case hDistinct =>
        intro z hz
        exact (List.pairwise_cons.mp (hDistinct z (Finset.mem_filter.mp hz).1)).2
      case hSeparate =>
        intro z hz w hw hEqual
        apply hSeparate z (Finset.mem_filter.mp hz).1 w (Finset.mem_filter.mp hw).1
        intro k hk
        exact (List.mem_cons.mp hk).elim
          (fun hki => by
            subst k
            exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm)
          (fun hkTail => hEqual k hkTail)
    have hFiber := Finset.sum_fiberwise_of_maps_to
      (s := s) (t := available) (g := fun z => f z i)
      (fun z hz => hMap z hz i (by simp))
      (fun z => hamiltonianRevealWeight A (i :: rows) available (f z))
    rw [<- hFiber]
    calc
      _ = available.sum (fun j => A i j / total *
          (s.filter (fun z => f z i = j)).sum
            (fun z => hamiltonianRevealWeight A rows (available.erase j) (f z))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        have hEq := (Finset.mem_filter.mp hz).2
        simp only [hamiltonianRevealWeight, hEq, total]
      _ <= available.sum (fun j => A i j / total) := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hBranch j) (div_nonneg (hA i j) hTotal)
      _ = total / total := by rw [<- Finset.sum_div]
      _ <= 1 := by
        by_cases hZero : total = 0
        case pos => rw [hZero, div_zero]; norm_num
        case neg => rw [div_self hZero]

end PrimeFactorOscillations
