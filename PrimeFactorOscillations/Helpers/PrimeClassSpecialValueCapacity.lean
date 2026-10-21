/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSpecialValueTests

/-!
# Complete infinite-capacity theorem for the three actual prime-value classes

Each certificate includes every positive-power sum, zero convergence
exponent, infinite capacity, all positive rational decoding powers and
correctness of an explicit finite membership procedure.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

theorem fermat_values_strictMono : StrictMono (fun n : Nat => 2 ^ (2 ^ n) + 1) := by
  intro m n hmn
  have hi : 2 ^ m < 2 ^ n := Nat.pow_lt_pow_right (by decide) hmn
  have ho : 2 ^ (2 ^ m) < 2 ^ (2 ^ n) := Nat.pow_lt_pow_right (by decide) hi
  change 2 ^ (2 ^ m) + 1 < 2 ^ (2 ^ n) + 1
  omega

theorem mersenne_values_strictMono : StrictMono (fun n : Nat => 2 ^ (n + 2) - 1) := by
  intro m n hmn
  have hp : 2 ^ (m + 2) < 2 ^ (n + 2) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hlo : 1 <= 2 ^ (m + 2) := Nat.one_le_pow _ _ (by decide)
  change 2 ^ (m + 2) - 1 < 2 ^ (n + 2) - 1
  omega

theorem fibonacci_values_from_three_strictMono :
    StrictMono (fun n : Nat => Nat.fib (n + 3)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hlo := fibonacci_shifted_index_le_value n
  have hrec : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) :=
    Nat.fib_add_two
  change Nat.fib (n + 3) < Nat.fib (n + 4)
  omega

theorem mersennePrimeValues_iff_index_ge_two (p : Nat) :
    Membership.mem mersennePrimeValues p <->
      And (Nat.Prime p) (exists m : Nat, And (2 <= m) (2 ^ m - 1 = p)) := by
  constructor
  case mp =>
    intro hp
    choose n hn using hp.2
    exact And.intro hp.1 (Exists.intro (n + 2) (And.intro (by omega) hn))
  case mpr =>
    intro hp
    choose m hm using hp.2
    apply And.intro hp.1
    apply Exists.intro (m - 2)
    have heq : m - 2 + 2 = m := by omega
    simpa only [heq] using hm.2

theorem fibonacci_prime_index_ge_three (n : Nat) (hp : Nat.Prime (Nat.fib n)) : 3 <= n := by
  by_contra hnot
  have hn : Or (n = 0) (Or (n = 1) (n = 2)) := by omega
  rcases hn with h0 | h1 | h2
  case inl => subst n; exact hp.ne_zero (by decide)
  case inr.inl => subst n; exact hp.ne_one (by decide)
  case inr.inr => subst n; exact hp.ne_one (by decide)

theorem fibonacciPrimeValues_iff_index_ge_three (p : Nat) :
    Membership.mem fibonacciPrimeValues p <->
      And (Nat.Prime p) (exists m : Nat, And (3 <= m) (Nat.fib m = p)) := by
  constructor
  case mp =>
    intro hp
    choose m hm using hp.2
    have hprime : Nat.Prime (Nat.fib m) := by rw [hm]; exact hp.1
    exact And.intro hp.1 (Exists.intro m
      (And.intro (fibonacci_prime_index_ge_three m hprime) hm))
  case mpr =>
    intro hp
    choose m hm using hp.2
    exact And.intro hp.1 (Exists.intro m hm.2)

structure PrimeValueCapacityCertificate (P : Set Nat) (test : Nat -> Bool) : Prop where
  positive_power_summable : forall s : Real, 0 < s -> Summable (classPowerWeight P s)
  zero_exponent : primeClassConvergenceExponent P = 0
  infinite_capacity : integerDecoderCapacity P = Top.top
  all_powers_admissible : forall h : Rat, 0 < h -> integerDecoderAdmissible P h
  membership_correct : forall p : Nat, test p = true <-> Membership.mem P p

theorem primeValueCapacityCertificate_of_all_positive_summable
    (P : Set Nat) (test : Nat -> Bool)
    (hsum : forall s : Real, 0 < s -> Summable (classPowerWeight P s))
    (htest : forall p : Nat, test p = true <-> Membership.mem P p) :
    PrimeValueCapacityCertificate P test := by
  have htau := primeClassConvergenceExponent_zero_of_all_positive_summable P hsum
  exact {
    positive_power_summable := hsum
    zero_exponent := htau
    infinite_capacity := integerDecoderCapacity_top_of_all_positive_summable P hsum
    all_powers_admissible := fun h hh =>
      integerDecoderAdmissible_of_zero_convergenceExponent P (1 / 2) (by norm_num)
        (by norm_num) (hsum _ (by norm_num)) htau h hh
    membership_correct := htest
  }

theorem special_prime_value_capacity :
    And (PrimeValueCapacityCertificate fermatPrimeValues fermatPrimeValueTest)
      (And (PrimeValueCapacityCertificate mersennePrimeValues mersennePrimeValueTest)
        (PrimeValueCapacityCertificate fibonacciPrimeValues fibonacciPrimeValueTest)) := by
  exact And.intro
    (primeValueCapacityCertificate_of_all_positive_summable fermatPrimeValues fermatPrimeValueTest
      fermatPrimeValues_all_positive_power_summable fermatPrimeValueTest_correct)
    (And.intro
      (primeValueCapacityCertificate_of_all_positive_summable mersennePrimeValues mersennePrimeValueTest
        mersennePrimeValues_all_positive_power_summable mersennePrimeValueTest_correct)
      (primeValueCapacityCertificate_of_all_positive_summable fibonacciPrimeValues fibonacciPrimeValueTest
        fibonacciPrimeValues_all_positive_power_summable fibonacciPrimeValueTest_correct))

end PrimeFactorOscillations.PrimeClassSampling
