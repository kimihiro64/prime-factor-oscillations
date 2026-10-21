/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassExponentialPrimeValues
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.FibonacciGoldenCarrier

/-!
# Binet's formula and infinite capacity of actual Fibonacci prime values

The real golden ratio supplies an unconditional exponential lower bound.
The class consists of prime values of the recurrence itself, without a
prime-index restriction or any assumption that infinitely many are prime.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

noncomputable def fibonacciPhi : Real := (1 + Real.sqrt 5) / 2

def fibonacciPrimeValues : Set Nat := primeValueClass Nat.fib

theorem fibonacciPhi_sq : fibonacciPhi ^ 2 = fibonacciPhi + 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : Real) <= 5)
  unfold fibonacciPhi
  nlinarith

theorem fibonacciPhi_bounds : And (1 < fibonacciPhi) (fibonacciPhi < 2) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : Real) <= 5)
  have hs0 := Real.sqrt_nonneg (5 : Real)
  unfold fibonacciPhi
  constructor <;> nlinarith

theorem fibonacciPhi_complement (n : Nat) :
    abs ((1 - fibonacciPhi) ^ n) <= 1 := by
  have hb := fibonacciPhi_bounds
  have hv : abs (1 - fibonacciPhi) <= 1 := abs_le.mpr (by constructor <;> linarith)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, abs_mul]
    have h0 := abs_nonneg ((1 - fibonacciPhi) ^ n)
    have h1 := abs_nonneg (1 - fibonacciPhi)
    nlinarith

theorem fibonacci_binet_real (n : Nat) :
    (Nat.fib n : Real) =
      (fibonacciPhi ^ n - (-(Inv.inv fibonacciPhi)) ^ n) / Real.sqrt 5 := by
  have hb := Fibonacci.fib_binet_mul fibonacciPhi (1 - fibonacciPhi)
    fibonacciPhi_sq (Fibonacci.golden_complement_sq fibonacciPhi fibonacciPhi_sq) n
  have hphi0 : 0 < fibonacciPhi := lt_trans zero_lt_one fibonacciPhi_bounds.1
  have hsqrt : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hdiff : fibonacciPhi - (1 - fibonacciPhi) = Real.sqrt 5 := by
    unfold fibonacciPhi
    ring
  have hv : 1 - fibonacciPhi = -(Inv.inv fibonacciPhi) := by
    calc
      1 - fibonacciPhi = -1 / fibonacciPhi := by
        apply (eq_div_iff (ne_of_gt hphi0)).mpr
        nlinarith [fibonacciPhi_sq]
      _ = -(Inv.inv fibonacciPhi) := by ring
  rw [hdiff, hv] at hb
  apply (eq_div_iff (ne_of_gt hsqrt)).mpr
  simpa only [mul_comm] using hb

theorem fibonacciPhi_pow_ge_two (n : Nat) (hn : 2 <= n) :
    2 <= fibonacciPhi ^ n := by
  have hb := fibonacciPhi_bounds
  have hall : forall k : Nat, 1 <= fibonacciPhi ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      exact one_le_mul_of_one_le_of_one_le ih (le_of_lt hb.1)
  have heq : n = (n - 2) + 2 := by omega
  rw [heq, pow_add]
  have hbase : (2 : Real) <= fibonacciPhi ^ 2 := by nlinarith [fibonacciPhi_sq]
  exact hbase.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hall (n - 2)) (sq_nonneg fibonacciPhi))

theorem fibonacci_golden_exponential_lower (n : Nat) (hn : 2 <= n) :
    fibonacciPhi ^ n / (2 * Real.sqrt 5) <= (Nat.fib n : Real) := by
  have hb := Fibonacci.fib_binet_mul fibonacciPhi (1 - fibonacciPhi)
    fibonacciPhi_sq (Fibonacci.golden_complement_sq fibonacciPhi fibonacciPhi_sq) n
  have hdiff : fibonacciPhi - (1 - fibonacciPhi) = Real.sqrt 5 := by
    unfold fibonacciPhi
    ring
  rw [hdiff] at hb
  have hv : (1 - fibonacciPhi) ^ n <= 1 :=
    (le_abs_self _).trans (fibonacciPhi_complement n)
  have hp := fibonacciPhi_pow_ge_two n hn
  have hsqrt : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  apply _root_.le_of_mul_le_mul_right ?_ (mul_pos (by norm_num : (0 : Real) < 2) hsqrt)
  calc
    (fibonacciPhi ^ n / (2 * Real.sqrt 5)) * (2 * Real.sqrt 5) = fibonacciPhi ^ n := by
      field_simp
    _ <= (Nat.fib n : Real) * (2 * Real.sqrt 5) := by nlinarith

theorem fibonacciPrimeValues_all_positive_power_summable
    (s : Real) (hs : 0 < s) : Summable (classPowerWeight fibonacciPrimeValues s) := by
  have hsqrt : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  apply primeValueClass_power_summable_of_exponential_growth Nat.fib fibonacciPhi
    (1 / (2 * Real.sqrt 5)) s fibonacciPhi_bounds.1 (by positivity) hs
  filter_upwards [eventually_ge_atTop 2] with n hn
  have h := fibonacci_golden_exponential_lower n hn
  convert h using 1
  ring

theorem fibonacciPrimeValues_convergenceExponent_zero :
    primeClassConvergenceExponent fibonacciPrimeValues = 0 :=
  primeClassConvergenceExponent_zero_of_all_positive_summable fibonacciPrimeValues
    fibonacciPrimeValues_all_positive_power_summable

theorem fibonacciPrimeValues_infinite_capacity : integerDecoderCapacity fibonacciPrimeValues = Top.top :=
  integerDecoderCapacity_top_of_all_positive_summable fibonacciPrimeValues
    fibonacciPrimeValues_all_positive_power_summable

end PrimeFactorOscillations.PrimeClassSampling
