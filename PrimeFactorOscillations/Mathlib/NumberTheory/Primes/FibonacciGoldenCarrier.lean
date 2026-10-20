/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.StrongDivisibilityCarrier

/-!
# Fibonacci divisibility as a golden-root multiplicative clock

Binet's identity over a ring connects the integer recurrence to powers of
roots of X^2-X-1. With distinct roots, vanishing is the power-one test for
their quotient, or -u^2 when the other root is 1-u. The integer entry points
of 2 and 5 are retained separately, including repeated-root characteristic five.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Fibonacci

/-- Binet's identity without division, over any commutative ring. -/
theorem fib_binet_mul {K : Type*} [CommRing K] (u v : K)
    (hu : u ^ 2 = u + 1) (hv : v ^ 2 = v + 1) (n : Nat) :
    (u - v) * (Nat.fib n : K) = u ^ n - v ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
    calc
      (u - v) * (Nat.fib (n + 2) : K) =
          (u - v) * (Nat.fib n : K) + (u - v) * (Nat.fib (n + 1) : K) := by
            rw [Nat.fib_add_two, Nat.cast_add]
            ring
      _ = (u ^ n - v ^ n) + (u ^ (n + 1) - v ^ (n + 1)) := by rw [ih0, ih1]
      _ = u ^ n * (u + 1) - v ^ n * (v + 1) := by
        rw [pow_succ, pow_succ]
        ring
      _ = u ^ n * u ^ 2 - v ^ n * v ^ 2 := by rw [hu, hv]
      _ = u ^ (n + 2) - v ^ (n + 2) := by rw [pow_add, pow_add]

/-- Fibonacci vanishing is the multiplicative clock of the quotient of distinct roots. -/
theorem fib_cast_eq_zero_iff_root_ratio_pow {K : Type*} [Field K] (u v : K)
    (hu : u ^ 2 = u + 1) (hv : v ^ 2 = v + 1)
    (hd : Not (u = v)) (hv0 : Not (v = 0)) (n : Nat) :
    (Nat.fib n : K) = 0 <-> (u / v) ^ n = 1 := by
  have hb := fib_binet_mul u v hu hv n
  have hz : (Nat.fib n : K) = 0 <-> u ^ n = v ^ n := by
    constructor
    { intro h
      rw [h, mul_zero] at hb
      exact sub_eq_zero.mp hb.symm }
    { intro h
      have hf : (u - v) * (Nat.fib n : K) = 0 := by rw [hb, h, sub_self]
      exact (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hd) }
  simpa only [div_pow, div_eq_one_iff_eq (pow_ne_zero n hv0)] using hz

theorem golden_complement_sq {K : Type*} [CommRing K] (u : K)
    (hu : u ^ 2 = u + 1) :
    (1 - u) ^ 2 = (1 - u) + 1 := by
  calc
    (1 - u) ^ 2 = u ^ 2 - 2 * u + 1 := by ring
    _ = (1 - u) + 1 := by rw [hu]; ring

theorem golden_root_product {K : Type*} [CommRing K] (u : K)
    (hu : u ^ 2 = u + 1) :
    u * (1 - u) = -1 := by
  calc
    u * (1 - u) = u - u ^ 2 := by ring
    _ = -1 := by rw [hu]; ring

theorem golden_root_quotient {K : Type*} [Field K] (u : K)
    (hu : u ^ 2 = u + 1) :
    u / (1 - u) = -(u ^ 2) := by
  have hprod := golden_root_product u hu
  have hv0 : Not ((1 - u) = 0) := by
    intro h
    have hc : (0 : K) = -1 := by simpa only [h, mul_zero] using hprod
    exact one_ne_zero (neg_eq_zero.mp hc.symm)
  apply (div_eq_iff hv0).mpr
  calc
    u = -u * (u * (1 - u)) := by rw [hprod]; ring
    _ = -(u ^ 2) * (1 - u) := by ring

/-- The unified golden-root power test underlying the entry point. -/
theorem fib_cast_eq_zero_iff_golden_pow {K : Type*} [Field K] (u : K)
    (hu : u ^ 2 = u + 1) (hsep : Not (u = 1 - u)) (n : Nat) :
    (Nat.fib n : K) = 0 <-> (-(u ^ 2)) ^ n = 1 := by
  have hprod := golden_root_product u hu
  have hv0 : Not ((1 - u) = 0) := by
    intro h
    have hc : (0 : K) = -1 := by simpa only [h, mul_zero] using hprod
    exact one_ne_zero (neg_eq_zero.mp hc.symm)
  rw [<- golden_root_quotient u hu]
  exact fib_cast_eq_zero_iff_root_ratio_pow u (1 - u) hu
    (golden_complement_sq u hu) hsep hv0 n

/-- Integer divisibility in characteristic r is the same power test. -/
theorem dvd_fib_iff_golden_pow {K : Type*} [Field K] (r : Nat) [CharP K r]
    (u : K) (hu : u ^ 2 = u + 1) (hsep : Not (u = 1 - u)) (n : Nat) :
    Dvd.dvd r (Nat.fib n) <-> (-(u ^ 2)) ^ n = 1 := by
  rw [<- CharP.cast_eq_zero_iff K r (Nat.fib n)]
  exact fib_cast_eq_zero_iff_golden_pow u hu hsep n

/-- A prime-index Fibonacci zero has exactly that golden-root order. -/
theorem golden_order_eq_prime_index {K : Type*} [Field K] (u : K)
    (hu : u ^ 2 = u + 1) (hsep : Not (u = 1 - u)) (l : Nat)
    (hl : Nat.Prime l) (hzero : (Nat.fib l : K) = 0) :
    orderOf (-(u ^ 2)) = l := by
  have hpow := (fib_cast_eq_zero_iff_golden_pow u hu hsep l).mp hzero
  have hdiv : Dvd.dvd (orderOf (-(u ^ 2))) l :=
    orderOf_dvd_iff_pow_eq_one.mpr hpow
  rcases (Nat.dvd_prime hl).mp hdiv with hone | heq
  { have hd1 : Dvd.dvd (orderOf (-(u ^ 2))) 1 := by
      rw [hone]
    have hpow1 : (-(u ^ 2)) ^ 1 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd1
    have hzero1 := (fib_cast_eq_zero_iff_golden_pow u hu hsep 1).mpr hpow1
    exact False.elim (one_ne_zero (by simpa only [Nat.fib_one, Nat.cast_one] using hzero1)) }
  { exact heq }

/-- The deterministic carrier realizes its label as a golden-root order. -/
theorem fibonacci_carrier_golden_order {K : Type*} [Field K] (l : Nat)
    [CharP K (Nat.fibonacciPrimeCarrier l)] (hl : Nat.Prime l)
    (u : K) (hu : u ^ 2 = u + 1) (hsep : Not (u = 1 - u)) :
    orderOf (-(u ^ 2)) = l := by
  apply golden_order_eq_prime_index u hu hsep l hl
  exact (CharP.cast_eq_zero_iff K (Nat.fibonacciPrimeCarrier l) (Nat.fib l)).mpr
    (Nat.fibonacciPrimeCarrier_dvd l)

end Fibonacci

namespace Nat

/-- The characteristic-two entry point is three. -/
theorem two_dvd_fib_iff_three_dvd (n : Nat) :
    Dvd.dvd 2 (fib n) <-> Dvd.dvd 3 n :=
  prime_dvd_fib_prime_index_iff 3 2 n (by decide) (by decide) (by decide)

/-- The repeated-root prime five has entry point five. -/
theorem five_dvd_fib_iff_five_dvd (n : Nat) :
    Dvd.dvd 5 (fib n) <-> Dvd.dvd 5 n :=
  prime_dvd_fib_prime_index_iff 5 5 n (by decide) (by decide) (by decide)

theorem fibonacciPrimeCarrier_three : fibonacciPrimeCarrier 3 = 2 := by decide

theorem fibonacciPrimeCarrier_five : fibonacciPrimeCarrier 5 = 5 := by
  have hp := fibonacciPrimeCarrier_prime 5 (by decide)
  have hd : Dvd.dvd (fibonacciPrimeCarrier 5) 5 := by
    simpa only [show fib 5 = 5 by decide] using fibonacciPrimeCarrier_dvd 5
  exact (prime_dvd_prime_iff_eq hp (by decide)).mp hd

end Nat
