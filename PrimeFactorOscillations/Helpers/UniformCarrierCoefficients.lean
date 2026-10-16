/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.Bertrand
import PrimeFactorOscillations.Helpers.UniformCarrierObservation

/-!
# Uniform Carrier Coefficients

Probability-derived coefficient arrays with degree-uniform error and exact treatment of small indices.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

theorem normalized_coefficient_bound (n : Nat) (hn : 0 < n) (c : Complex)
    (hc : norm c <= (n : Real)) : norm (c / (n : Complex)) <= 1 := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_one hnR).mpr hc

structure CoefficientObservation (d n : Nat) (c : Complex) (hc : norm c <= (n : Real)) where
  degree_pos : 1 <= d
  index_pos : 0 < n
  prime : Nat.Primes
  lower : n ^ d < (prime : Nat)
  upper : (prime : Nat) <= 2 * n ^ d
  carrier : Observation 1 (n ^ d) (singletonMark (n ^ d) prime (c / (n : Complex)))
    (singletonMark_bound (n ^ d) prime upper (c / (n : Complex))
      (normalized_coefficient_bound n index_pos c hc))

def CoefficientObservation.value {d n : Nat} {c : Complex} {hc : norm c <= (n : Real)}
    (O : CoefficientObservation d n c hc) : Complex :=
  (n : Complex) * (((2 * ((n ^ d : Nat) : Real) : Real) : Complex)) * O.carrier.value

theorem exists_probability_coefficients :
    exists n0 : Nat, exists C : Real, 100 <= n0 /\ 0 < C /\
      forall d : Nat, 2 <= d ->
      forall f : Nat -> Complex, forall hf : (forall n, norm (f n) <= (n : Real)),
      exists a : Nat -> Complex,
        (forall n : Nat, Not (n = 0) ->
          norm (a n - f n) <= C / (n : Real) ^ (d - 1)) /\
        (forall n : Nat, n0 <= n ->
          exists O : CoefficientObservation d n (f n) (hf n), a n = O.value) /\
        (forall n : Nat, n < n0 -> a n = f n) := by
  choose P0 C hP0 hC hObs using exists_singleton_observation 1 zero_lt_one
  let n0 := max 100 P0
  refine Exists.intro n0 (Exists.intro C
    (And.intro (le_max_left _ _) (And.intro hC ?_)))
  intro d hd f hf
  have hPoint : forall n : Nat, n0 <= n ->
      exists O : CoefficientObservation d n (f n) (hf n),
        norm (O.value - f n) <= C / (n : Real) ^ (d - 1) := by
    intro n hn0
    have hn100 : 100 <= n := (le_max_left _ _).trans hn0
    have hn : 0 < n := by omega
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hnC : Not ((n : Complex) = 0) := by exact_mod_cast (Nat.ne_of_gt hn)
    have hPow : n <= n ^ d := by
      calc
        n = n ^ 1 := by simp
        _ <= n ^ d := by gcongr <;> omega
    have hP : P0 <= n ^ d := ((le_max_right _ _).trans hn0).trans hPow
    choose p hpPrime hpLo hpHi using
      Nat.exists_prime_lt_and_le_two_mul (n ^ d) (pow_ne_zero d (Nat.ne_of_gt hn))
    let prime : Nat.Primes := Subtype.mk p hpPrime
    let z := f n / (n : Complex)
    have hz : norm z <= 1 := normalized_coefficient_bound n hn (f n) (hf n)
    choose O hO using hObs (n ^ d) hP prime hpLo hpHi z hz
    let W : CoefficientObservation d n (f n) (hf n) :=
      @CoefficientObservation.mk d n (f n) (hf n) (by omega) hn prime hpLo hpHi O
    refine Exists.intro W ?_
    have hid : W.value - f n =
        (n : Complex) *
          (((2 * ((n ^ d : Nat) : Real) : Real) : Complex) * O.value - z) := by
      change (n : Complex) * (((2 * ((n ^ d : Nat) : Real) : Real) : Complex)) *
        O.value - f n = _
      dsimp [z]
      field_simp [hnC]
    rw [hid, norm_mul, Complex.norm_natCast]
    calc
      _ <= (n : Real) * (C / ((n ^ d : Nat) : Real)) :=
        mul_le_mul_of_nonneg_left hO (Nat.cast_nonneg n)
      _ = C / (n : Real) ^ (d - 1) := by
        rw [Nat.cast_pow]
        have hExp : d = (d - 1) + 1 := by omega
        have hPowEq : (n : Real) ^ d = (n : Real) ^ (d - 1) * (n : Real) := by
          conv_lhs => rw [hExp, pow_succ]
        rw [hPowEq]
        field_simp [hnR.ne'] <;> ring
  let a : Nat -> Complex := fun n =>
    if h : n0 <= n then (Classical.choose (hPoint n h)).value else f n
  refine Exists.intro a (And.intro ?_ (And.intro ?_ ?_))
  . intro n hn
    by_cases h : n0 <= n
    . simpa only [a, dif_pos h] using Classical.choose_spec (hPoint n h)
    . simp only [a, dif_neg h, sub_self, norm_zero]
      exact div_nonneg hC.le (pow_nonneg (Nat.cast_nonneg n) _)
  . intro n hn
    refine Exists.intro (Classical.choose (hPoint n hn)) ?_
    simp only [a, dif_pos hn]
  . intro n hn
    have hnot : Not (n0 <= n) := by omega
    simp only [a, dif_neg hnot]

end PrimeFactorOscillations.UniformCarrier
