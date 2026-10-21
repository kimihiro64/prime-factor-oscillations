/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CapacitySelectionFinite

/-!
# Decreasing weighted costs under complete prefix dominance

The existing exact signed slack sum retains every count surplus and every
weight difference. It yields the weighted comparison and the strict equality
criterion needed by the actual capped-prime rank theorem.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem selectionCost_le_of_prefix_dominance
    (g t : Nat -> Prop) (w : Nat -> Real) (n : Nat)
    (hcount : forall k : Nat, k <= n -> selectionCount t k <= selectionCount g k)
    (hwn : 0 <= w n)
    (hw : forall k : Nat, k < n -> w (k + 1) <= w k) :
    selectionCost t w n <= selectionCost g w n := by
  have hs := selection_slack_sum g t w n
  have hsum : (Finset.range n).sum (fun k =>
      (((selectionCount g (k + 1) : Nat) : Real) -
        ((selectionCount t (k + 1) : Nat) : Real)) * (w (k + 1) - w k)) <= 0 := by
    apply Finset.sum_nonpos
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    exact mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (Nat.cast_le.mpr (hcount (k + 1) (by omega))))
      (sub_nonpos.mpr (hw k hkn))
  have hlast : 0 <=
      (((selectionCount g n : Nat) : Real) - ((selectionCount t n : Nat) : Real)) * w n :=
    mul_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr (hcount n le_rfl))) hwn
  linarith only [hs, hsum, hlast]

theorem selectionCount_eq_of_strict_cost_tie
    (g t : Nat -> Prop) (w : Nat -> Real) (n : Nat)
    (hcount : forall k : Nat, k <= n -> selectionCount t k <= selectionCount g k)
    (hwn : 0 < w n)
    (hw : forall k : Nat, k < n -> w (k + 1) < w k)
    (hcost : selectionCost g w n = selectionCost t w n) :
    forall k : Nat, k <= n -> selectionCount g k = selectionCount t k := by
  let d : Nat -> Real := fun k => (selectionCount g k : Real) - (selectionCount t k : Real)
  let f : Nat -> Real := fun k => d (k + 1) * (w (k + 1) - w k)
  have hd : forall k : Nat, k <= n -> 0 <= d k := by
    intro k hk
    exact sub_nonneg.mpr (Nat.cast_le.mpr (hcount k hk))
  have hf : forall k : Nat, k < n -> f k <= 0 := by
    intro k hk
    exact mul_nonpos_of_nonneg_of_nonpos (hd (k + 1) (by omega))
      (sub_nonpos.mpr (hw k hk).le)
  have hsum : (Finset.range n).sum f <= 0 := by
    apply Finset.sum_nonpos
    intro k hk
    exact hf k (Finset.mem_range.mp hk)
  have hs : d n * w n = (Finset.range n).sum f := by
    have h := selection_slack_sum g t w n
    rw [hcost, sub_self, sub_zero] at h
    exact h
  have hprod : d n * w n <= 0 := hs.le.trans hsum
  have hdn : d n = 0 := by
    apply le_antisymm _ (hd n le_rfl)
    by_contra h
    have hp : 0 < d n := lt_of_not_ge h
    have hpos := mul_pos hp hwn
    linarith only [hpos, hprod]
  have hsumzero : (Finset.range n).sum f = 0 := by
    simpa only [hdn, zero_mul] using hs.symm
  have hnegSum : (Finset.range n).sum (fun k => -(f k)) = 0 := by
    rw [Finset.sum_neg_distrib, hsumzero, neg_zero]
  intro k hk
  cases k with
  | zero => rfl
  | succ j =>
    have hj : j < n := by omega
    have hsingle : -(f j) <= (Finset.range n).sum (fun k => -(f k)) :=
      Finset.single_le_sum
        (fun k hkm => neg_nonneg.mpr (hf k (Finset.mem_range.mp hkm)))
        (Finset.mem_range.mpr hj)
    rw [hnegSum] at hsingle
    have hfj : f j = 0 := by
      apply le_antisymm (hf j hj)
      linarith only [hsingle]
    have hzero : d (j + 1) = 0 := by
      have hmul : d (j + 1) * (w (j + 1) - w j) = 0 := hfj
      exact (mul_eq_zero.mp hmul).resolve_right (sub_neg.mpr (hw j hj)).ne
    have heq : (selectionCount g (j + 1) : Real) =
        (selectionCount t (j + 1) : Real) := by
      change (selectionCount g (j + 1) : Real) -
        (selectionCount t (j + 1) : Real) = 0 at hzero
      linarith only [hzero]
    exact_mod_cast heq

theorem selection_eq_of_strict_cost_tie
    (g t : Nat -> Prop) (w : Nat -> Real) (n : Nat)
    (hcount : forall k : Nat, k <= n -> selectionCount t k <= selectionCount g k)
    (hwn : 0 < w n)
    (hw : forall k : Nat, k < n -> w (k + 1) < w k)
    (hcost : selectionCost g w n = selectionCost t w n) :
    forall k : Nat, k < n -> (g k <-> t k) := by
  classical
  have heq := selectionCount_eq_of_strict_cost_tie g t w n hcount hwn hw hcost
  intro k hk
  have hpre := heq k (by omega)
  have hsucc := heq (k + 1) (by omega)
  constructor
  case mp =>
    intro hg
    by_contra ht
    simp only [selectionCount, ite_eq_left hg, ite_eq_right ht, Nat.add_zero] at hsucc
    omega
  case mpr =>
    intro ht
    by_contra hg
    simp only [selectionCount, ite_eq_right hg, ite_eq_left ht, Nat.add_zero] at hsucc
    omega

end PrimeFactorOscillations.PrimeClassDeletion
