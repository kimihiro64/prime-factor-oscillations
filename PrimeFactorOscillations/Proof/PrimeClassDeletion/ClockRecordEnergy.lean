/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyRegulator

/-! # Exact signed energy of the existing positive-record clock

The energy retains the full terminal slack. The quadratic variation is
the sum of the actual record increments squared. No cancellation estimate
or zero-free improvement is assumed or asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

def clockPreviousError (e : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => e n

noncomputable def clockRecordIncrement (e : Nat -> Real) (n : Nat) : Real :=
  clockRecord e (n + 1) - clockRecord e n

noncomputable def clockRecordSignedEnergy (e : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => clockRecordSignedEnergy e n +
      clockRecord e n * (e n - clockPreviousError e n)

noncomputable def clockRecordQuadraticVariation (e : Nat -> Real) (n : Nat) : Real :=
  (Finset.range n).sum (fun i => (clockRecordIncrement e i) ^ 2)

theorem clockRecordIncrement_nonneg (e : Nat -> Real) (n : Nat) :
    0 <= clockRecordIncrement e n := by
  change 0 <= max (clockRecord e n) (e n) - clockRecord e n
  exact sub_nonneg.mpr (le_max_left _ _)

theorem clockRecordIncrement_sum (e : Nat -> Real) (n : Nat) :
    (Finset.range n).sum (clockRecordIncrement e) = clockRecord e n := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, clockRecord]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, clockRecordIncrement]
      ring

theorem clockRecordSignedEnergy_eq_sum (e : Nat -> Real) (n : Nat) :
    clockRecordSignedEnergy e n =
      (Finset.range n).sum (fun i => clockRecord e i * (e i - clockPreviousError e i)) := by
  induction n with
  | zero => simp only [clockRecordSignedEnergy, Finset.range_zero, Finset.sum_empty]
  | succ n ih => rw [clockRecordSignedEnergy, Finset.sum_range_succ, ih]

theorem clockRecordQuadraticVariation_succ (e : Nat -> Real) (n : Nat) :
    clockRecordQuadraticVariation e (n + 1) =
      clockRecordQuadraticVariation e n +
        (clockRecord e (n + 1) - clockRecord e n) ^ 2 := by
  simp only [clockRecordQuadraticVariation, Finset.sum_range_succ, clockRecordIncrement]

theorem clockRecordSignedEnergy_identity (e : Nat -> Real) (n : Nat) :
    (clockRecord e n) ^ 2 = 2 * clockRecordSignedEnergy e n +
      2 * clockRecord e n * (clockRecord e n - clockPreviousError e n) +
        clockRecordQuadraticVariation e n := by
  induction n with
  | zero =>
      simp only [clockRecord, clockRecordSignedEnergy, clockPreviousError,
        clockRecordQuadraticVariation, Finset.range_zero, Finset.sum_empty,
        zero_pow (by decide : Not (2 = 0)), mul_zero, add_zero, sub_self]
  | succ n ih =>
      rw [clockRecordQuadraticVariation_succ]
      simp only [clockRecordSignedEnergy]
      rw [show clockPreviousError e (n + 1) = e n from rfl]
      by_cases h : clockRecord e n <= e n
      case pos =>
        have hnext : clockRecord e (n + 1) = e n := max_eq_right h
        rw [hnext]
        nlinarith only [ih]
      case neg =>
        have hnext : clockRecord e (n + 1) = clockRecord e n :=
          max_eq_left (le_of_lt (lt_of_not_ge h))
        rw [hnext]
        nlinarith only [ih]

theorem clockRecordQuadraticVariation_nonneg (e : Nat -> Real) (n : Nat) :
    0 <= clockRecordQuadraticVariation e n :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (clockRecordIncrement e i))

theorem clockRecordQuadraticVariation_le (e : Nat -> Real) (n : Nat) (W : Real)
    (hW : forall i : Nat, i < n -> clockRecordIncrement e i <= W) :
    clockRecordQuadraticVariation e n <= W * clockRecord e n := by
  calc
    clockRecordQuadraticVariation e n <=
        (Finset.range n).sum (fun i => W * clockRecordIncrement e i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hW i (Finset.mem_range.mp hi))
        (clockRecordIncrement_nonneg e i)
    _ = W * clockRecord e n := by
      rw [<- Finset.mul_sum, clockRecordIncrement_sum]

theorem clockRecordIncrement_le_of_clock (e w : Nat -> Real)
    (hw : forall i : Nat, 0 <= w i) (hinit : e 0 <= w 0)
    (hclock : forall i : Nat, e (i + 1) <= e i + w (i + 1)) (n : Nat) :
    clockRecordIncrement e n <= w n := by
  have hpre : e n <= clockRecord e n + w n := by
    cases n with
    | zero => simpa only [clockRecord, zero_add] using hinit
    | succ k =>
        have he := clockRecord_contains e k
        have hc := hclock k
        linarith only [he, hc]
  change max (clockRecord e n) (e n) - clockRecord e n <= w n
  have hmax : max (clockRecord e n) (e n) <= clockRecord e n + w n :=
    max_le (le_add_of_nonneg_right (hw n)) hpre
  linarith only [hmax]

theorem clockRecordSignedEnergy_at_record (e : Nat -> Real) (n : Nat)
    (hrecord : clockPreviousError e n = clockRecord e n) :
    (clockRecord e n) ^ 2 =
      2 * clockRecordSignedEnergy e n + clockRecordQuadraticVariation e n := by
  simpa only [hrecord, sub_self, mul_zero, add_zero] using
    clockRecordSignedEnergy_identity e n

end PrimeFactorOscillations.PrimeClassDeletion
