/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact signed slack for actual prime overweight

The primal-dual gap splits into three nonnegative signed contact slacks.
Equality forces the zero/capacity/repair classification used by the finite
polynomial dual. This file does not prove polynomial dual attainment or an
analytic power-saving estimate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

def overweightGap (a w p : Real) : Real :=
  max (w - a) 0 - (w * p - a * max p 0)

theorem overweight_gap_decomposition (a w p : Real) :
    overweightGap a w p =
      (1 - max p 0) * max (w - a) 0 +
      max p 0 * max (a - w) 0 + max (-p) 0 * w := by
  unfold overweightGap
  by_cases hwa : a <= w
  case pos =>
    have hw : 0 <= w - a := sub_nonneg.mpr hwa
    have ha : a - w <= 0 := sub_nonpos.mpr hwa
    rw [max_eq_left hw, max_eq_right ha]
    by_cases hp : 0 <= p
    case pos =>
      have hn : -p <= 0 := neg_nonpos.mpr hp
      rw [max_eq_left hp, max_eq_right hn]
      nlinarith
    case neg =>
      have hp0 : p <= 0 := (lt_of_not_ge hp).le
      have hn : 0 <= -p := neg_nonneg.mpr hp0
      rw [max_eq_right hp0, max_eq_left hn]
      nlinarith
  case neg =>
    have hwa0 : w <= a := (lt_of_not_ge hwa).le
    have hw : w - a <= 0 := sub_nonpos.mpr hwa0
    have ha : 0 <= a - w := sub_nonneg.mpr hwa0
    rw [max_eq_right hw, max_eq_left ha]
    by_cases hp : 0 <= p
    case pos =>
      have hn : -p <= 0 := neg_nonpos.mpr hp
      rw [max_eq_left hp, max_eq_right hn]
      nlinarith
    case neg =>
      have hp0 : p <= 0 := (lt_of_not_ge hp).le
      have hn : 0 <= -p := neg_nonneg.mpr hp0
      rw [max_eq_right hp0, max_eq_left hn]
      nlinarith

theorem overweight_gap_nonneg (a w p : Real)
    (hw : 0 <= w) (hp : p <= 1) :
    0 <= overweightGap a w p := by
  rw [overweight_gap_decomposition]
  have hp1 : max p 0 <= 1 := max_le hp zero_le_one
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (sub_nonneg.mpr hp1) (le_max_right (w - a) 0))
      (mul_nonneg (le_max_right p 0) (le_max_right (a - w) 0)))
    (mul_nonneg (le_max_right (-p) 0) hw)

theorem weighted_atom_le_overweight (a w p : Real)
    (hw : 0 <= w) (hp : p <= 1) :
    w * p - a * max p 0 <= max (w - a) 0 := by
  have h := overweight_gap_nonneg a w p hw hp
  unfold overweightGap at h
  linarith

theorem overweight_gap_sum {I : Type*} (S : Finset I)
    (a w p : I -> Real) :
    S.sum (fun i => overweightGap (a i) (w i) (p i)) =
      S.sum (fun i => max (w i - a i) 0) -
        (S.sum (fun i => w i * p i) -
          S.sum (fun i => a i * max (p i) 0)) := by
  simp only [overweightGap, Finset.sum_sub_distrib]

theorem optimal_overweight_contacts {I : Type*} (S : Finset I)
    (a w p : I -> Real)
    (hw : forall i, Membership.mem S i -> 0 <= w i)
    (hp : forall i, Membership.mem S i -> p i <= 1)
    (hopt : S.sum (fun i => max (w i - a i) 0) =
      S.sum (fun i => w i * p i) -
        S.sum (fun i => a i * max (p i) 0)) :
    forall i, Membership.mem S i ->
      overweightGap (a i) (w i) (p i) = 0 := by
  have hnonneg : forall i, Membership.mem S i ->
      0 <= overweightGap (a i) (w i) (p i) := by
    intro i hi
    exact overweight_gap_nonneg (a i) (w i) (p i) (hw i hi) (hp i hi)
  have hsum : S.sum (fun i => overweightGap (a i) (w i) (p i)) = 0 := by
    rw [overweight_gap_sum, hopt, sub_self]
  intro i hi
  have hle : overweightGap (a i) (w i) (p i) <=
      S.sum (fun j => overweightGap (a j) (w j) (p j)) :=
    Finset.single_le_sum hnonneg hi
  rw [hsum] at hle
  exact le_antisymm hle (hnonneg i hi)

theorem overweight_contact_classification (a w p : Real)
    (hw : 0 <= w) (hz : overweightGap a w p = 0) :
    (p < 0 -> w = 0) /\
    (p = 0 -> w <= a) /\
    (0 < p -> p < 1 -> w = a) /\
    (p = 1 -> a <= w) := by
  have heq : max (w - a) 0 = w * p - a * max p 0 := by
    unfold overweightGap at hz
    linarith
  have he0 : 0 <= max (w - a) 0 := le_max_right (w - a) 0
  apply And.intro
  case left =>
    intro hp
    have hp0 : p <= 0 := hp.le
    rw [max_eq_right hp0, mul_zero, sub_zero] at heq
    have hwp : w * p = 0 :=
      le_antisymm (mul_nonpos_of_nonneg_of_nonpos hw hp0) (by linarith)
    exact (mul_eq_zero.mp hwp).resolve_right (ne_of_lt hp)
  case right =>
    apply And.intro
    case left =>
      intro hp
      subst p
      simp only [max_self, mul_zero, sub_zero] at heq
      have hwa : w - a <= 0 := by
        have h := le_max_left (w - a) 0
        linarith
      exact sub_nonpos.mp hwa
    case right =>
      apply And.intro
      case left =>
        intro hp hp1
        rw [max_eq_left hp.le] at heq
        by_cases hwa : a <= w
        case pos =>
          rw [max_eq_left (sub_nonneg.mpr hwa)] at heq
          have hprod : (w - a) * (1 - p) = 0 := by nlinarith
          have hfactor : Not (1 - p = 0) := by linarith
          have hdiff := (mul_eq_zero.mp hprod).resolve_right hfactor
          linarith
        case neg =>
          have hwa0 : w <= a := (lt_of_not_ge hwa).le
          rw [max_eq_right (sub_nonpos.mpr hwa0)] at heq
          have hprod : (w - a) * p = 0 := by nlinarith
          have hdiff := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hp)
          linarith
      case right =>
        intro hp
        subst p
        simp only [max_eq_left zero_le_one, mul_one] at heq
        have hwa : 0 <= w - a := by linarith
        exact sub_nonneg.mp hwa

end PrimeFactorOscillations.PrimeClassDeletion
