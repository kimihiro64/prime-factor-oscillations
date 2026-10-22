/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.ClockRecordEnergy

/-! # Signed finite product ledger for the record process

These identities retain the prime supply before the continuous integral is
inserted. A positive record jump is charged at the actual new record value.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem clockRecordIncrement_complementarity (e : Nat -> Real) (n : Nat) :
    e n * clockRecordIncrement e n =
      clockRecord e (n + 1) * clockRecordIncrement e n := by
  by_cases h : clockRecord e n <= e n
  case pos =>
    have hnext : clockRecord e (n + 1) = e n := max_eq_right h
    rw [hnext]
  case neg =>
    have hnext : clockRecord e (n + 1) = clockRecord e n :=
      max_eq_left (le_of_lt (lt_of_not_ge h))
    simp only [clockRecordIncrement, hnext, sub_self, mul_zero]

theorem clockRecord_product_ledger (e a : Nat -> Real) (n : Nat) :
    clockRecord e n * a n =
      (Finset.range n).sum (fun i => clockRecord e i * (a (i + 1) - a i)) +
        (Finset.range n).sum (fun i => a (i + 1) * clockRecordIncrement e i) := by
  induction n with
  | zero => simp only [clockRecord, Finset.range_zero, Finset.sum_empty, zero_mul, zero_add]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, clockRecordIncrement]
      nlinarith only [ih]

theorem clockRecord_error_product (e : Nat -> Real) (n : Nat) :
    clockRecord e n * clockPreviousError e n = clockRecordSignedEnergy e n +
      (Finset.range n).sum
        (fun i => clockRecord e (i + 1) * clockRecordIncrement e i) := by
  rw [clockRecordSignedEnergy_eq_sum]
  calc
    _ = (Finset.range n).sum
          (fun i => clockRecord e i * (clockPreviousError e (i + 1) -
            clockPreviousError e i)) +
        (Finset.range n).sum
          (fun i => clockPreviousError e (i + 1) * clockRecordIncrement e i) :=
      clockRecord_product_ledger e (clockPreviousError e) n
    _ = _ := by
      have hright :
          (Finset.range n).sum
            (fun i => clockPreviousError e (i + 1) * clockRecordIncrement e i) =
          (Finset.range n).sum
            (fun i => clockRecord e (i + 1) * clockRecordIncrement e i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact clockRecordIncrement_complementarity e i
      rw [hright]
      rfl

theorem clockRecord_right_jump_energy (e : Nat -> Real) (n : Nat) :
    2 * (Finset.range n).sum
        (fun i => clockRecord e (i + 1) * clockRecordIncrement e i) =
      (clockRecord e n) ^ 2 + clockRecordQuadraticVariation e n := by
  have hproduct := clockRecord_error_product e n
  have henergy := clockRecordSignedEnergy_identity e n
  nlinarith only [hproduct, henergy]

end PrimeFactorOscillations.PrimeClassDeletion
