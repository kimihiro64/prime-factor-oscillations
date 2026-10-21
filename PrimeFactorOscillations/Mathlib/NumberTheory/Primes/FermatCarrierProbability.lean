/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.FermatCarrier

/-!
# The actual finite probability law of nested Fermat carriers

The sampled exponent ranges over a complete dyadic period. Even and odd
exponents give an exact recursion, hence a truncated geometric generating
polynomial. Its compensation identity is valid even at z=2; the quotient
and error identities retain the nonzero-denominator hypothesis explicitly.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- The number of dyadic divisibility events among the first k thresholds. -/
def truncatedDyadicCount (k n : Nat) : Nat :=
  (Finset.range k).sum (fun j => if Dvd.dvd (2 ^ (j + 1)) n then 1 else 0)

/-- Actual selected prime factors of Fermat numbers, tested on 2^n-1. -/
def fermatCarrierCount (k n : Nat) : Nat :=
  (Finset.range k).sum
    (fun j => if Dvd.dvd (fermatPrimeCarrier j) (2 ^ n - 1) then 1 else 0)

theorem truncatedDyadicCount_zero (n : Nat) : truncatedDyadicCount 0 n = 0 := by
  simp [truncatedDyadicCount]

theorem truncatedDyadicCount_at_zero (k : Nat) : truncatedDyadicCount k 0 = k := by
  simp [truncatedDyadicCount]

theorem dyadic_power_dvd_two_mul (j n : Nat) :
    Dvd.dvd (2 ^ (j + 1 + 1)) (2 * n) <-> Dvd.dvd (2 ^ (j + 1)) n := by
  rw [pow_succ, Nat.mul_comm 2 n]
  exact Nat.mul_dvd_mul_iff_right (by decide : 0 < 2)

theorem truncatedDyadicCount_succ_even (k n : Nat) :
    truncatedDyadicCount (k + 1) (2 * n) = 1 + truncatedDyadicCount k n := by
  unfold truncatedDyadicCount
  rw [Finset.sum_range_succ']
  have htwo : Dvd.dvd 2 (2 * n) := dvd_mul_right 2 n
  simp only [dyadic_power_dvd_two_mul, zero_add, pow_one, ite_eq_left htwo]
  exact Nat.add_comm _ _

theorem truncatedDyadicCount_succ_odd (k n : Nat) :
    truncatedDyadicCount (k + 1) (2 * n + 1) = 0 := by
  unfold truncatedDyadicCount
  apply Finset.sum_eq_zero
  intro j _
  have hn : Not (Dvd.dvd (2 ^ (j + 1)) (2 * n + 1)) := by
    intro hd
    apply (odd_two_mul_add_one n).not_two_dvd_nat
    apply dvd_trans ?_ hd
    rw [pow_succ]
    exact dvd_mul_left 2 (2 ^ j)
  simp only [ite_eq_right hn]

theorem fermatCarrierCount_eq_dyadic (k n : Nat) :
    fermatCarrierCount k n = truncatedDyadicCount k n := by
  unfold fermatCarrierCount truncatedDyadicCount
  apply Finset.sum_congr rfl
  intro j _
  simp only [fermatPrimeCarrier_mersenne_iff]

end Nat

namespace FermatProbability

private theorem sum_range_two_mul {A : Type*} [AddCommMonoid A]
    (f : Nat -> A) (m : Nat) :
    (Finset.range (2 * m)).sum f =
      (Finset.range m).sum (fun n => f (2 * n) + f (2 * n + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have he : 2 * (m + 1) = (2 * m + 1) + 1 := by rw [Nat.mul_succ]
    rw [he, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    exact add_assoc _ _ _

/-- The unnormalized generating sum of the actual dyadic index sample. -/
def sampleSum {K : Type*} [CommSemiring K] (k : Nat) (z : K) : K :=
  (Finset.range (2 ^ k)).sum (fun n => z ^ Nat.truncatedDyadicCount k n)

theorem sampleSum_zero {K : Type*} [CommSemiring K] (z : K) :
    sampleSum 0 z = 1 := by
  simp [sampleSum, Nat.truncatedDyadicCount]

/-- This recurrence retains the full dependence of all dyadic events. -/
theorem sampleSum_succ {K : Type*} [CommSemiring K] (k : Nat) (z : K) :
    sampleSum (k + 1) z = (2 : K) ^ k + z * sampleSum k z := by
  unfold sampleSum
  rw [pow_succ', sum_range_two_mul]
  simp only [Nat.truncatedDyadicCount_succ_even, Nat.truncatedDyadicCount_succ_odd,
    pow_add, pow_one, pow_zero]
  rw [Finset.sum_add_distrib, <- Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Nat.cast_pow, Nat.cast_ofNat]
  exact add_comm _ _

/-- A denominator-free identity, including the point z=2. -/
theorem sampleSum_compensation {K : Type*} [CommRing K] (k : Nat) (z : K) :
    (2 - z) * sampleSum k z = (2 : K) ^ k + (1 - z) * z ^ k := by
  induction k with
  | zero =>
    rw [sampleSum_zero]
    simp only [pow_zero, mul_one]
    ring
  | succ k ih =>
    rw [sampleSum_succ]
    calc
      (2 - z) * ((2 : K) ^ k + z * sampleSum k z) =
          (2 - z) * (2 : K) ^ k + z * ((2 - z) * sampleSum k z) := by ring
      _ = (2 - z) * (2 : K) ^ k + z * ((2 : K) ^ k + (1 - z) * z ^ k) := by rw [ih]
      _ = (2 : K) ^ (k + 1) + (1 - z) * z ^ (k + 1) := by
        rw [pow_succ, pow_succ]
        ring

/-- Actual Fermat prime-factor events give precisely this generating sum. -/
theorem actual_sample_sum_eq {K : Type*} [CommSemiring K] (k : Nat) (z : K) :
    (Finset.range (2 ^ k)).sum (fun n => z ^ Nat.fermatCarrierCount k n) =
      sampleSum k z := by
  simp only [Nat.fermatCarrierCount_eq_dyadic]
  rfl

/-- Uniform sampling over one complete period, in a characteristic-zero field. -/
def samplePGF {K : Type*} [Field K] (k : Nat) (z : K) : K :=
  sampleSum k z / (2 : K) ^ k

theorem samplePGF_zero {K : Type*} [Field K] (z : K) :
    samplePGF 0 z = 1 := by
  simp [samplePGF, sampleSum_zero]

theorem samplePGF_succ {K : Type*} [Field K] [CharZero K] (k : Nat) (z : K) :
    samplePGF (k + 1) z = 1 / 2 + (z / 2) * samplePGF k z := by
  unfold samplePGF
  rw [sampleSum_succ, pow_succ]
  have ht : Not ((2 : K) = 0) := two_ne_zero
  have hp : Not ((2 : K) ^ k = 0) := pow_ne_zero k ht
  field_simp [ht, hp]

theorem samplePGF_eq_geometric {K : Type*} [Field K] [CharZero K] (k : Nat) (z : K) :
    samplePGF k z =
      ((Finset.range k).sum (fun t => (z / 2) ^ t)) / 2 + (z / 2) ^ k := by
  induction k with
  | zero => simp [samplePGF_zero]
  | succ k ih =>
    have hs : (Finset.range k).sum (fun t => (z / 2) ^ (t + 1)) =
        (z / 2) * (Finset.range k).sum (fun t => (z / 2) ^ t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      exact pow_succ' _ _
    rw [samplePGF_succ, ih, Finset.sum_range_succ', hs, pow_succ']
    simp only [pow_zero]
    ring

theorem samplePGF_compensation {K : Type*} [Field K] [CharZero K] (k : Nat) (z : K) :
    (2 - z) * samplePGF k z = 1 + (1 - z) * (z / 2) ^ k := by
  have hp : Not ((2 : K) ^ k = 0) := pow_ne_zero k two_ne_zero
  unfold samplePGF
  calc
    (2 - z) * (sampleSum k z / (2 : K) ^ k) =
        ((2 - z) * sampleSum k z) / (2 : K) ^ k := by ring
    _ = ((2 : K) ^ k + (1 - z) * z ^ k) / (2 : K) ^ k := by
      rw [sampleSum_compensation]
    _ = 1 + (1 - z) * (z / 2) ^ k := by
      rw [add_div, div_self hp, div_pow]
      ring

/-- The exact error is used only off the displayed denominator zero. -/
theorem samplePGF_error {K : Type*} [Field K] [CharZero K]
    (k : Nat) (z : K) (hz : Not (z = 2)) :
    samplePGF k z - 1 / (2 - z) = (1 - z) * (z / 2) ^ k / (2 - z) := by
  have hd : Not ((2 : K) - z = 0) := sub_ne_zero.mpr (Ne.symm hz)
  calc
    samplePGF k z - 1 / (2 - z) =
        ((2 - z) * samplePGF k z - 1) / (2 - z) := by
      field_simp [hd]
    _ = (1 - z) * (z / 2) ^ k / (2 - z) := by
      rw [samplePGF_compensation]
      ring

/-- z=2 is finite at every stage; it is not evaluated by a singular quotient. -/
theorem samplePGF_two {K : Type*} [Field K] [CharZero K] (k : Nat) :
    samplePGF k (2 : K) = 1 + (k : K) / 2 := by
  rw [samplePGF_eq_geometric]
  simp only [div_self (two_ne_zero : Not ((2 : K) = 0)), one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact add_comm _ _

/-- The exact total count over one full sample period. -/
theorem sampleCount_sum (k : Nat) :
    (Finset.range (2 ^ k)).sum (Nat.truncatedDyadicCount k) = 2 ^ k - 1 := by
  induction k with
  | zero => simp [Nat.truncatedDyadicCount]
  | succ k ih =>
    calc
      (Finset.range (2 ^ (k + 1))).sum (Nat.truncatedDyadicCount (k + 1)) =
          (Finset.range (2 ^ k)).sum (fun n => 1 + Nat.truncatedDyadicCount k n) := by
            rw [pow_succ', sum_range_two_mul]
            simp only [Nat.truncatedDyadicCount_succ_even,
              Nat.truncatedDyadicCount_succ_odd, add_zero]
      _ = 2 ^ k + (2 ^ k - 1) := by
        rw [Finset.sum_add_distrib, ih]
        simp
      _ = 2 ^ (k + 1) - 1 := by
        rw [<- Nat.add_sub_assoc Nat.one_le_two_pow, pow_succ', two_mul]

/-- The actual sample mean of the selected Fermat prime-factor count. -/
def sampleMean {K : Type*} [Field K] (k : Nat) : K :=
  (((Finset.range (2 ^ k)).sum (Nat.fermatCarrierCount k) : Nat) : K) / (2 : K) ^ k

theorem sampleMean_eq {K : Type*} [Field K] [CharZero K] (k : Nat) :
    sampleMean (K := K) k = 1 - 1 / (2 : K) ^ k := by
  unfold sampleMean
  simp only [Nat.fermatCarrierCount_eq_dyadic]
  rw [sampleCount_sum, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one, sub_div, div_self (pow_ne_zero k (two_ne_zero : Not ((2 : K) = 0)))]

end FermatProbability
