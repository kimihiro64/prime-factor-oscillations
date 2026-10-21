/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact deleted-prime counts and partial capacity

For nonnegative weights on an explicitly finite support, the deficit below
unit capacity equals the number of zero weights plus the retained fractional
deficits. These statements are the finite consumer for the ordinary rational
LP vertex construction. No analytic estimate or RH statement is proved here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable section

def zeroWeightSupport {I : Type*} (S : Finset I) (w : I -> Real) : Finset I :=
  S.filter (fun i => w i = 0)

def partialWeightSupport {I : Type*} (S : Finset I) (w : I -> Real) : Finset I :=
  S.filter (fun i => 0 < w i /\ w i < 1)

def unitCapacityDeficit {I : Type*} (S : Finset I) (w : I -> Real) : Real :=
  S.sum (fun i => max (1 - w i) 0)

theorem unitCapacityDeficit_atom (w : Real) (hw : 0 <= w) :
    max (1 - w) 0 =
      (if w = 0 then 1 else 0) +
        (if 0 < w /\ w < 1 then 1 - w else 0) := by
  by_cases hz : w = 0
  case pos =>
    subst w
    simp
  case neg =>
    have hp : 0 < w := lt_of_le_of_ne hw (Ne.symm hz)
    by_cases h1 : w < 1
    case pos =>
      rw [ite_eq_right hz, ite_eq_left (And.intro hp h1),
        max_eq_left (sub_nonneg.mpr h1.le), zero_add]
    case neg =>
      have h1w : 1 <= w := not_lt.mp h1
      have hnot : Not (0 < w /\ w < 1) := fun h => h1 h.2
      rw [ite_eq_right hz, ite_eq_right hnot,
        max_eq_right (sub_nonpos.mpr h1w), zero_add]

theorem unitCapacityDeficit_eq_zero_count_add_partial {I : Type*}
    (S : Finset I) (w : I -> Real)
    (hw : forall i, Membership.mem S i -> 0 <= w i) :
    unitCapacityDeficit S w =
      ((zeroWeightSupport S w).card : Real) +
        (partialWeightSupport S w).sum (fun i => 1 - w i) := by
  unfold unitCapacityDeficit zeroWeightSupport partialWeightSupport
  calc
    _ = S.sum (fun i =>
        (if w i = 0 then 1 else 0) +
          (if 0 < w i /\ w i < 1 then 1 - w i else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact unitCapacityDeficit_atom (w i) (hw i hi)
    _ = _ := by
      simp only [Finset.sum_add_distrib, <- Finset.sum_filter,
        Finset.sum_const, nsmul_eq_mul, mul_one]

theorem partialWeightDeficit_nonneg {I : Type*}
    (S : Finset I) (w : I -> Real) :
    0 <= (partialWeightSupport S w).sum (fun i => 1 - w i) := by
  apply Finset.sum_nonneg
  intro i hi
  have hpart := (Finset.mem_filter.mp hi).2
  exact sub_nonneg.mpr (le_of_lt hpart.2)

theorem partialWeightDeficit_le_count {I : Type*}
    (S : Finset I) (w : I -> Real) :
    (partialWeightSupport S w).sum (fun i => 1 - w i) <=
      ((partialWeightSupport S w).card : Real) := by
  calc
    _ <= (partialWeightSupport S w).sum (fun _ => (1 : Real)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hpart := (Finset.mem_filter.mp hi).2
      linarith [hpart.1]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

theorem zeroWeightCount_le_deficit {I : Type*}
    (S : Finset I) (w : I -> Real)
    (hw : forall i, Membership.mem S i -> 0 <= w i) :
    ((zeroWeightSupport S w).card : Real) <= unitCapacityDeficit S w := by
  rw [unitCapacityDeficit_eq_zero_count_add_partial S w hw]
  have hp := partialWeightDeficit_nonneg S w
  linarith

theorem deficit_le_zeroWeightCount_add_partialCount {I : Type*}
    (S : Finset I) (w : I -> Real)
    (hw : forall i, Membership.mem S i -> 0 <= w i) :
    unitCapacityDeficit S w <=
      ((zeroWeightSupport S w).card : Real) +
        ((partialWeightSupport S w).card : Real) := by
  rw [unitCapacityDeficit_eq_zero_count_add_partial S w hw]
  have hp := partialWeightDeficit_le_count S w
  linarith

theorem deficit_sub_zeroWeightCount_bounds {I : Type*}
    (S : Finset I) (w : I -> Real)
    (hw : forall i, Membership.mem S i -> 0 <= w i) :
    0 <= unitCapacityDeficit S w - ((zeroWeightSupport S w).card : Real) /\
      unitCapacityDeficit S w - ((zeroWeightSupport S w).card : Real) <=
        ((partialWeightSupport S w).card : Real) := by
  apply And.intro
  case left =>
    have h := zeroWeightCount_le_deficit S w hw
    linarith
  case right =>
    have h := deficit_le_zeroWeightCount_add_partialCount S w hw
    linarith

end

end PrimeFactorOscillations.PrimeClassDeletion
