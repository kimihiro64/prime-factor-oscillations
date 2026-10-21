/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderIntegerSize

/-!
# An integer Horner algorithm for the actual probes

A step computes the coefficient index, multiplies the accumulator and the
scaled coefficient, adds them and doubles the stored power of two: five
arithmetic operations. The counter records this explicit arithmetic model.
Input-count acquisition is excluded. Two operations form the signed input
at each point, and one sign comparison is charged for each adjacent pair.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

structure DecoderHornerState where
  accumulator : Int
  twoPower : Nat
  arithmeticSteps : Nat

def integerHornerState (C : Nat -> Nat) (x : Int) (M : Nat) :
    Nat -> DecoderHornerState
  | 0 => { accumulator := 0, twoPower := 1, arithmeticSteps := 0 }
  | j + 1 =>
    let previous := integerHornerState C x M j
    { accumulator := x * previous.accumulator +
        (C (M - j) : Int) * (previous.twoPower : Int)
      twoPower := 2 * previous.twoPower
      arithmeticSteps := previous.arithmeticSteps + 5 }

theorem integerHornerState_twoPower (C : Nat -> Nat) (x : Int) (M j : Nat) :
    (integerHornerState C x M j).twoPower = 2 ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [integerHornerState, ih, pow_succ, Nat.mul_comm]

theorem integerHornerState_arithmeticSteps (C : Nat -> Nat) (x : Int) (M j : Nat) :
    (integerHornerState C x M j).arithmeticSteps = 5 * j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [integerHornerState]
    rw [ih]
    omega

theorem integerHornerState_sum (C : Nat -> Nat) (x : Int) (M j : Nat) :
    (integerHornerState C x M j).accumulator =
      (Finset.range j).sum (fun i =>
        (C (M - i) : Int) * x ^ (j - 1 - i) * (2 : Int) ^ i) := by
  induction j with
  | zero => simp [integerHornerState]
  | succ j ih =>
    change x * (integerHornerState C x M j).accumulator +
        (C (M - j) : Int) * ((integerHornerState C x M j).twoPower : Int) = _
    rw [ih, integerHornerState_twoPower, Nat.cast_pow, Nat.cast_ofNat]
    have hsum :
        x * (Finset.range j).sum (fun i =>
          (C (M - i) : Int) * x ^ (j - 1 - i) * (2 : Int) ^ i) =
        (Finset.range j).sum (fun i =>
          (C (M - i) : Int) * x ^ (j - i) * (2 : Int) ^ i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < j := Finset.mem_range.mp hi
      have hexp : j - i = (j - 1 - i) + 1 := by omega
      rw [hexp, pow_succ]
      ring
    rw [hsum, Finset.sum_range_succ]
    have hexp : (j + 1) - 1 = j := by omega
    simp only [hexp, Nat.sub_self, pow_zero, mul_one]

theorem integerHornerState_eq_integerProbe (M n : Nat) (C : Nat -> Nat) :
    (integerHornerState C (-((2 * n + 1 : Nat) : Int)) M (M + 1)).accumulator =
      integerProbe M C n := by
  rw [integerHornerState_sum, integerProbe]
  rw [<- Finset.sum_range_reflect
    (fun k => (-1 : Int) ^ k * (C k : Int) *
      ((2 * n + 1 : Nat) : Int) ^ k * (2 : Int) ^ (M - k)) (M + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hiM : i <= M := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hreverse : M - (M - i) = i := by omega
  have hexp : M + 1 - 1 = M := by omega
  simp only [hexp, hreverse]
  rw [neg_pow]
  ring

def integerHornerTotalOperations (R M : Nat) : Nat :=
  (R + 1) * (5 * (M + 1) + 2) + R

theorem integerHorner_total_operation_bound (R M : Nat) (hR : 1 <= R) (hM : 1 <= M) :
    integerHornerTotalOperations R M <= 25 * R * M := by
  unfold integerHornerTotalOperations
  have hr : R + 1 <= 2 * R := by omega
  have hm : 5 * (M + 1) + 2 <= 12 * M := by omega
  calc
    (R + 1) * (5 * (M + 1) + 2) + R <= (2 * R) * (12 * M) + R := by
      gcongr
    _ <= 25 * R * M := by nlinarith

end PrimeFactorOscillations.PrimeClassDecoder
