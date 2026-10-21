/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassFibonacciGrowth

/-!
# Finite membership tests for the three actual special prime-value classes

An elementary index bound makes membership a bounded integer search.
The Fibonacci test includes every index; its repeated nonprime values
at the beginning introduce no exceptional prime labels.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

theorem fibonacci_shifted_index_le_value (n : Nat) : n + 1 <= Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih0 ih1 =>
    have heq : Nat.fib (n + 2 + 2) = Nat.fib (n + 2) + Nat.fib (n + 1 + 2) := by
      rw [Nat.fib_add_two]
    rw [heq]
    omega

theorem fibonacci_index_le_value_add_two (n : Nat) : n <= Nat.fib n + 2 := by
  by_cases hn : 2 <= n
  case pos =>
    have h := fibonacci_shifted_index_le_value (n - 2)
    have heq : n - 2 + 2 = n := by omega
    rw [heq] at h
    omega
  case neg => omega

def primeValueTest (f : Nat -> Nat) (B p : Nat) : Bool :=
  decide (Nat.Prime p) && (List.range (p + B + 1)).any (fun n => decide (f n = p))

theorem primeValueTest_eq_true_iff
    (f : Nat -> Nat) (B : Nat) (hbound : forall n, n <= f n + B) (p : Nat) :
    primeValueTest f B p = true <-> Membership.mem (primeValueClass f) p := by
  simp only [primeValueTest, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range]
  constructor
  case mp =>
    intro hp
    choose n hn using hp.2
    exact And.intro hp.1 (Exists.intro n hn.2)
  case mpr =>
    intro hp
    choose n hn using hp.2
    have hnb := hbound n
    rw [hn] at hnb
    exact And.intro hp.1 (Exists.intro n (And.intro (by omega) hn))

def fermatPrimeValueTest (p : Nat) : Bool := primeValueTest (fun n => 2 ^ (2 ^ n) + 1) 0 p

def mersennePrimeValueTest (p : Nat) : Bool := primeValueTest (fun n => 2 ^ (n + 2) - 1) 0 p

def fibonacciPrimeValueTest (p : Nat) : Bool := primeValueTest Nat.fib 2 p

theorem fermatPrimeValueTest_correct (p : Nat) :
    fermatPrimeValueTest p = true <-> Membership.mem fermatPrimeValues p := by
  apply primeValueTest_eq_true_iff
  intro n
  have hn := PrimeFactorOscillations.PrimeClassDecoder.nat_succ_le_two_pow n
  have hf := fermat_value_ge_two_pow n
  omega

theorem mersennePrimeValueTest_correct (p : Nat) :
    mersennePrimeValueTest p = true <-> Membership.mem mersennePrimeValues p := by
  apply primeValueTest_eq_true_iff
  intro n
  have hn := PrimeFactorOscillations.PrimeClassDecoder.nat_succ_le_two_pow n
  have hm := mersenne_value_ge_two_pow n
  omega

theorem fibonacciPrimeValueTest_correct (p : Nat) :
    fibonacciPrimeValueTest p = true <-> Membership.mem fibonacciPrimeValues p :=
  primeValueTest_eq_true_iff Nat.fib 2 fibonacci_index_le_value_add_two p

end PrimeFactorOscillations.PrimeClassSampling
