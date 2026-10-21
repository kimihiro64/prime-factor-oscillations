/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.FermatCarrierProbability

/-!
# Exact weighted nested-dyadic sampling

Arbitrary natural weights remain coupled by the common divisibility index.
Complete-period sampling gives a mixture at the cumulative weights, not a
product of individual Bernoulli polynomials.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- The cumulative weight of the first t nested events. -/
def dyadicPrefixWeight (w : Nat -> Nat) (t : Nat) : Nat :=
  (Finset.range t).sum w

/-- Weighted events along one scalar index, including index zero. -/
def weightedDyadicCount (w : Nat -> Nat) (k n : Nat) : Nat :=
  (Finset.range k).sum (fun j => if Dvd.dvd (2 ^ (j + 1)) n then w j else 0)

theorem dyadicPrefixWeight_zero (w : Nat -> Nat) : dyadicPrefixWeight w 0 = 0 := by
  simp [dyadicPrefixWeight]

theorem dyadicPrefixWeight_succ (w : Nat -> Nat) (t : Nat) :
    dyadicPrefixWeight w (t + 1) = w 0 + dyadicPrefixWeight (fun j => w (j + 1)) t := by
  unfold dyadicPrefixWeight
  rw [Finset.sum_range_succ']
  exact Nat.add_comm _ _

theorem weightedDyadicCount_zero (w : Nat -> Nat) (n : Nat) :
    weightedDyadicCount w 0 n = 0 := by
  simp [weightedDyadicCount]

theorem weightedDyadicCount_succ_even (w : Nat -> Nat) (k n : Nat) :
    weightedDyadicCount w (k + 1) (2 * n) =
      w 0 + weightedDyadicCount (fun j => w (j + 1)) k n := by
  unfold weightedDyadicCount
  rw [Finset.sum_range_succ']
  have htwo : Dvd.dvd 2 (2 * n) := dvd_mul_right 2 n
  simp only [dyadic_power_dvd_two_mul, zero_add, pow_one, ite_eq_left htwo]
  exact Nat.add_comm _ _

theorem weightedDyadicCount_succ_odd (w : Nat -> Nat) (k n : Nat) :
    weightedDyadicCount w (k + 1) (2 * n + 1) = 0 := by
  unfold weightedDyadicCount
  apply Finset.sum_eq_zero
  intro j _
  have hn : Not (Dvd.dvd (2 ^ (j + 1)) (2 * n + 1)) := by
    intro hd
    apply (odd_two_mul_add_one n).not_two_dvd_nat
    apply dvd_trans ?_ hd
    rw [pow_succ]
    exact dvd_mul_left 2 (2 ^ j)
  exact ite_eq_right hn

end Nat

namespace WeightedDyadicProbability

-- The corresponding arbitrary-function lemma in the unweighted owner is private.
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

/-- The actual unnormalized complete-period generating sum. -/
def sampleSum {K : Type*} [CommSemiring K] (w : Nat -> Nat) (k : Nat) (z : K) : K :=
  (Finset.range (2 ^ k)).sum (fun n => z ^ Nat.weightedDyadicCount w k n)

theorem sampleSum_zero {K : Type*} [CommSemiring K] (w : Nat -> Nat) (z : K) :
    sampleSum w 0 z = 1 := by
  simp [sampleSum, Nat.weightedDyadicCount]

theorem sampleSum_succ {K : Type*} [CommSemiring K]
    (w : Nat -> Nat) (k : Nat) (z : K) :
    sampleSum w (k + 1) z =
      (2 : K) ^ k + z ^ (w 0) * sampleSum (fun j => w (j + 1)) k z := by
  unfold sampleSum
  rw [pow_succ', sum_range_two_mul]
  simp only [Nat.weightedDyadicCount_succ_even, Nat.weightedDyadicCount_succ_odd,
    pow_add, pow_zero]
  rw [Finset.sum_add_distrib, <- Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Nat.cast_pow, Nat.cast_ofNat]
  exact add_comm _ _

/-- A scalar uniform over 0 <= n < 2^k. -/
def samplePGF {K : Type*} [Field K] (w : Nat -> Nat) (k : Nat) (z : K) : K :=
  sampleSum w k z / (2 : K) ^ k

theorem samplePGF_zero {K : Type*} [Field K] (w : Nat -> Nat) (z : K) :
    samplePGF w 0 z = 1 := by
  simp [samplePGF, sampleSum_zero]

theorem samplePGF_succ {K : Type*} [Field K] [CharZero K]
    (w : Nat -> Nat) (k : Nat) (z : K) :
    samplePGF w (k + 1) z =
      1 / 2 + (z ^ (w 0) / 2) * samplePGF (fun j => w (j + 1)) k z := by
  unfold samplePGF
  rw [sampleSum_succ, pow_succ]
  have ht : Not ((2 : K) = 0) := two_ne_zero
  have hp : Not ((2 : K) ^ k = 0) := pow_ne_zero k ht
  field_simp [ht, hp]

/-- The exact weighted geometric mixture at cumulative weights. -/
theorem samplePGF_eq_prefix {K : Type*} [Field K] [CharZero K]
    (w : Nat -> Nat) (k : Nat) (z : K) :
    samplePGF w k z =
      ((Finset.range k).sum (fun t =>
        z ^ Nat.dyadicPrefixWeight w t / (2 : K) ^ t)) / 2 +
        z ^ Nat.dyadicPrefixWeight w k / (2 : K) ^ k := by
  induction k generalizing w with
  | zero => simp [samplePGF_zero, Nat.dyadicPrefixWeight_zero]
  | succ k ih =>
    have hs : (Finset.range k).sum (fun t =>
        z ^ Nat.dyadicPrefixWeight w (t + 1) / (2 : K) ^ (t + 1)) =
        (z ^ (w 0) / 2) * (Finset.range k).sum (fun t =>
          z ^ Nat.dyadicPrefixWeight (fun j => w (j + 1)) t / (2 : K) ^ t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [Nat.dyadicPrefixWeight_succ, pow_add, pow_succ']
      exact (div_mul_div_comm (z ^ (w 0)) (2 : K)
        (z ^ Nat.dyadicPrefixWeight (fun j => w (j + 1)) t) ((2 : K) ^ t)).symm
    rw [samplePGF_succ, ih, Finset.sum_range_succ', hs,
      Nat.dyadicPrefixWeight_zero, Nat.dyadicPrefixWeight_succ, pow_add, pow_succ]
    simp only [pow_zero, div_one]
    have ht : Not ((2 : K) = 0) := two_ne_zero
    have hp : Not ((2 : K) ^ k = 0) := pow_ne_zero k ht
    field_simp [ht, hp]
    ring

end WeightedDyadicProbability
