/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSequenceSummability

/-!
# Actual Fermat and Mersenne prime values have infinite decoding capacity

The Mersenne index starts at two. The class is the set of prime values,
so duplicates and overlaps have no multiplicity, and no assertion about
the infinitude of either prime class is assumed or concluded.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

def primeValueClass (f : Nat -> Nat) : Set Nat :=
  fun p => And (Nat.Prime p) (exists n, f n = p)

def fermatPrimeValues : Set Nat := primeValueClass (fun n => 2 ^ (2 ^ n) + 1)

def mersennePrimeValues : Set Nat := primeValueClass (fun n => 2 ^ (n + 2) - 1)

theorem primeValueClass_power_summable_of_exponential_growth
    (f : Nat -> Nat) (A C s : Real) (hA : 1 < A) (hC : 0 < C) (hs : 0 < s)
    (hgrowth : Filter.Eventually (fun n : Nat => C * A ^ n <= (f n : Real)) atTop) :
    Summable (classPowerWeight (primeValueClass f) s) := by
  apply classPowerWeight_summable_of_sequence_cover (primeValueClass f) f s
  case hcover =>
    intro p _ hp
    exact hp.2
  exact sequence_power_summable_of_eventual_exponential_growth f A C s hA hC hs hgrowth

theorem fermat_value_ge_two_pow (n : Nat) : 2 ^ n <= 2 ^ (2 ^ n) + 1 := by
  have hindex : n <= 2 ^ n := by
    have h := PrimeFactorOscillations.PrimeClassDecoder.nat_succ_le_two_pow n
    omega
  exact (Nat.pow_le_pow_right (by norm_num : 1 <= 2) hindex).trans (Nat.le_succ _)

theorem mersenne_value_ge_two_pow (n : Nat) : 2 ^ n <= 2 ^ (n + 2) - 1 := by
  have hp : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
  have heq : 2 ^ (n + 2) = 4 * 2 ^ n := by
    rw [pow_add]
    norm_num
    ring
  omega

theorem fermatPrimeValues_all_positive_power_summable
    (s : Real) (hs : 0 < s) : Summable (classPowerWeight fermatPrimeValues s) := by
  apply primeValueClass_power_summable_of_exponential_growth
    (fun n => 2 ^ (2 ^ n) + 1) 2 1 s (by norm_num) (by norm_num) hs
  apply Filter.Eventually.of_forall
  intro n
  simpa only [one_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using
    (show ((2 ^ n : Nat) : Real) <= ((2 ^ (2 ^ n) + 1 : Nat) : Real) by
      exact_mod_cast fermat_value_ge_two_pow n)

theorem mersennePrimeValues_all_positive_power_summable
    (s : Real) (hs : 0 < s) : Summable (classPowerWeight mersennePrimeValues s) := by
  apply primeValueClass_power_summable_of_exponential_growth
    (fun n => 2 ^ (n + 2) - 1) 2 1 s (by norm_num) (by norm_num) hs
  apply Filter.Eventually.of_forall
  intro n
  simpa only [one_mul, Nat.cast_pow, Nat.cast_ofNat] using
    (show ((2 ^ n : Nat) : Real) <= ((2 ^ (n + 2) - 1 : Nat) : Real) by
      exact_mod_cast mersenne_value_ge_two_pow n)

theorem fermatPrimeValues_convergenceExponent_zero :
    primeClassConvergenceExponent fermatPrimeValues = 0 :=
  primeClassConvergenceExponent_zero_of_all_positive_summable fermatPrimeValues
    fermatPrimeValues_all_positive_power_summable

theorem mersennePrimeValues_convergenceExponent_zero :
    primeClassConvergenceExponent mersennePrimeValues = 0 :=
  primeClassConvergenceExponent_zero_of_all_positive_summable mersennePrimeValues
    mersennePrimeValues_all_positive_power_summable

theorem fermatPrimeValues_infinite_capacity : integerDecoderCapacity fermatPrimeValues = Top.top :=
  integerDecoderCapacity_top_of_all_positive_summable fermatPrimeValues
    fermatPrimeValues_all_positive_power_summable

theorem mersennePrimeValues_infinite_capacity : integerDecoderCapacity mersennePrimeValues = Top.top :=
  integerDecoderCapacity_top_of_all_positive_summable mersennePrimeValues
    mersennePrimeValues_all_positive_power_summable

end PrimeFactorOscillations.PrimeClassSampling
