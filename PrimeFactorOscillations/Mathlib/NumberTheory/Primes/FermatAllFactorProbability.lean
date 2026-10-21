/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.FermatFactorCount
import PrimeFactorOscillations.Mathlib.Probability.Distributions.WeightedDyadic

/-!
# The actual probability law of all Fermat prime factors

The supported observable counts every distinct prime factor in the selected
Fermat blocks. Their supports are disjoint, while every event within one
block is identical. Index zero is retained through finite supported
divisibility, not through the prime-factor set of zero.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- All distinct physical prime factors in the first k Fermat blocks. -/
def fermatFactorSupport (k : Nat) : Finset Nat :=
  (Finset.range k).biUnion (fun j => (2 ^ (2 ^ j) + 1).primeFactors)

/-- Actual supported divisibility along 2^n-1, including n=0. -/
def fermatAllCarrierCount (k n : Nat) : Nat :=
  ((fermatFactorSupport k).filter (fun r => Dvd.dvd r (2 ^ n - 1))).card

theorem fermat_primeFactors_filter (j n : Nat) :
    ((2 ^ (2 ^ j) + 1).primeFactors.filter (fun r => Dvd.dvd r (2 ^ n - 1))) =
      if Dvd.dvd (2 ^ (j + 1)) n then (2 ^ (2 ^ j) + 1).primeFactors else
        (EmptyCollection.emptyCollection : Finset Nat) := by
  by_cases hn : Dvd.dvd (2 ^ (j + 1)) n
  { rw [ite_eq_left hn]
    apply Finset.filter_eq_self.mpr
    intro r hr
    have hp := mem_primeFactors.mp hr
    exact (prime_factor_fermat_mersenne_iff j r n hp.1 hp.2.1).mpr hn }
  { rw [ite_eq_right hn]
    apply Finset.ext
    intro r
    constructor
    { intro hr
      have h := Finset.mem_filter.mp hr
      have hp := mem_primeFactors.mp h.1
      exact False.elim (hn ((prime_factor_fermat_mersenne_iff j r n hp.1 hp.2.1).mp h.2)) }
    { intro hr
      simp at hr } }

/-- Counts the full union once, retaining every prime within each block. -/
theorem fermatAllCarrierCount_eq_weighted (k n : Nat) :
    fermatAllCarrierCount k n = weightedDyadicCount fermatFactorCount k n := by
  have hdis : (Finset.range k : Set Nat).PairwiseDisjoint
      (fun j => (2 ^ (2 ^ j) + 1).primeFactors.filter
        (fun r => Dvd.dvd r (2 ^ n - 1))) := by
    intro i _ j _ hij
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (fermat_primeFactors_disjoint i j hij)
  unfold fermatAllCarrierCount fermatFactorSupport
  rw [Finset.filter_biUnion, Finset.card_biUnion hdis]
  unfold weightedDyadicCount
  apply Finset.sum_congr rfl
  intro j _
  rw [fermat_primeFactors_filter]
  by_cases hn : Dvd.dvd (2 ^ (j + 1)) n
  { simp only [ite_eq_left hn]
    rfl }
  { simp [hn] }

end Nat

namespace FermatAllFactorProbability

/-- Uniform complete-period PGF of the actual full supported prime count. -/
def samplePGF {K : Type*} [Field K] (k : Nat) (z : K) : K :=
  ((Finset.range (2 ^ k)).sum (fun n => z ^ Nat.fermatAllCarrierCount k n)) /
    (2 : K) ^ k

theorem samplePGF_eq_weighted {K : Type*} [Field K] (k : Nat) (z : K) :
    samplePGF k z = WeightedDyadicProbability.samplePGF Nat.fermatFactorCount k z := by
  unfold samplePGF WeightedDyadicProbability.samplePGF WeightedDyadicProbability.sampleSum
  simp only [Nat.fermatAllCarrierCount_eq_weighted]

/-- The complete physical prime-factor count has a weighted geometric law. -/
theorem samplePGF_eq_prefix {K : Type*} [Field K] [CharZero K] (k : Nat) (z : K) :
    samplePGF k z =
      ((Finset.range k).sum (fun t =>
        z ^ Nat.dyadicPrefixWeight Nat.fermatFactorCount t / (2 : K) ^ t)) / 2 +
        z ^ Nat.dyadicPrefixWeight Nat.fermatFactorCount k / (2 : K) ^ k := by
  rw [samplePGF_eq_weighted]
  exact WeightedDyadicProbability.samplePGF_eq_prefix Nat.fermatFactorCount k z

end FermatAllFactorProbability
