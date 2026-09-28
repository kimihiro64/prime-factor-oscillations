import PrimeFactorOscillations.Helpers.GenericOddPrefix
import PrimeFactorOscillations.Helpers.PrimeWeightAllowance

set_option autoImplicit false

/-!
# Uniform allowances on the actual density-ratio prefixes

Distinctness is retained when converting a prime list to its finite support.
The result is uniform in the cutoff, the prefix length, and the fixed positive
integer used to make the tail weights small.
-/

namespace PrimeFactorOscillations

/-- Ordinary odds on any list of distinct primes satisfy the finite-set bound. -/
theorem ordinary_primeList_allowance (entries : List Nat) (hn : entries.Nodup)
    (hp : forall p, List.Mem p entries -> Nat.Prime p) (M : Nat) (hM : 0 < M) :
    (entries.map PrimeFactorUnimodality.primeWeight).sum <=
      (M : Rat) + 1 + (entries.length : Rat) / (M : Rat) := by
  have h := ordinary_primeWeight_allowance entries.toFinset
    (fun p hp' => hp p (List.mem_toFinset.mp hp')) M hM
  rwa [List.sum_toFinset _ hn, List.toFinset_card_of_nodup hn] at h

/-- Generic odds on any list of distinct primes satisfy the same bound. -/
theorem genericOdd_primeList_allowance (entries : List Nat) (hn : entries.Nodup)
    (hp : forall p, List.Mem p entries -> Nat.Prime p) (M : Nat) (hM : 0 < M) :
    (entries.map genericOddWeight).sum <=
      (M : Rat) + 1 + (entries.length : Rat) / (M : Rat) := by
  have h := genericOdd_primeWeight_allowance entries.toFinset
    (fun p hp' => hp p (List.mem_toFinset.mp hp')) M hM
  rwa [List.sum_toFinset _ hn, List.toFinset_card_of_nodup hn] at h

/-- The canonical ordinary prime list has no repeated entries. -/
theorem ordinary_prefix_nodup (x : Nat) :
    (PrimeFactorUnimodality.primesBelow x).Nodup := by
  exact Finset.sort_nodup _ _

/-- Filtering the zero-probability prime preserves distinctness. -/
theorem odd_prefix_nodup (x : Nat) : (oddPrimesBelow x).Nodup := by
  exact List.Nodup.filter (fun p => decide (2 < p)) (ordinary_prefix_nodup x)

/-- Every entry of the positive odd prefix is prime. -/
theorem odd_prefix_prime (x p : Nat) (hp : List.Mem p (oddPrimesBelow x)) :
    Nat.Prime p := by
  exact (PrimeFactorUnimodality.primesBelow_entries x p (List.mem_filter.mp hp).1).1

/-- Uniform allowance for the first `r` ordinary odds, at every cutoff. -/
theorem ordinary_prefix_allowance (x r M : Nat) (hM : 0 < M) :
    (((PrimeFactorUnimodality.primesBelow x).map
      PrimeFactorUnimodality.primeWeight).take r).sum <=
        (M : Rat) + 1 + (r : Rat) / (M : Rat) := by
  rw [<- List.map_take]
  have h := ordinary_primeList_allowance _
    ((List.take_sublist r _).nodup (ordinary_prefix_nodup x))
    (fun p hp => (PrimeFactorUnimodality.primesBelow_entries x p
      (List.mem_of_mem_take hp)).1) M hM
  have hlen : (((PrimeFactorUnimodality.primesBelow x).take r).length : Rat) <=
      (r : Rat) := by exact_mod_cast List.length_take_le r (PrimeFactorUnimodality.primesBelow x)
  have hdiv := div_le_div_of_nonneg_right hlen (Nat.cast_nonneg M : (0 : Rat) <= M)
  exact h.trans (by linarith)

/-- The exact largest-weight prefix occurring in the generic ratio denominator. -/
theorem genericOdd_prefix_allowance (x r M : Nat) (hM : 0 < M) :
    (((oddPrimesBelow x).map genericOddWeight).take r).sum <=
      (M : Rat) + 1 + (r : Rat) / (M : Rat) := by
  rw [<- List.map_take]
  have h := genericOdd_primeList_allowance _
    ((List.take_sublist r _).nodup (odd_prefix_nodup x))
    (fun p hp => odd_prefix_prime x p (List.mem_of_mem_take hp)) M hM
  have hlen : (((oddPrimesBelow x).take r).length : Rat) <= (r : Rat) := by
    exact_mod_cast List.length_take_le r (oddPrimesBelow x)
  have hdiv := div_le_div_of_nonneg_right hlen (Nat.cast_nonneg M : (0 : Rat) <= M)
  exact h.trans (by linarith)

/-- The full generic sum also controls the number of available positive trials. -/
theorem genericOdd_weightSum_card_bound (x M : Nat) (hM : 0 < M) :
    genericOddPrimeWeightSum x <=
      (M : Rat) + 1 + ((oddPrimesBelow x).length : Rat) / (M : Rat) := by
  rw [<- genericOdd_sum_oddPrimesBelow]
  exact genericOdd_primeList_allowance _ (odd_prefix_nodup x) (odd_prefix_prime x) M hM

/-- The corresponding full-support estimate for ordinary prime weights. -/
theorem ordinary_weightSum_card_bound (x M : Nat) (hM : 0 < M) :
    ordinaryPrimeWeightSum x <=
      (M : Rat) + 1 + ((PrimeFactorUnimodality.primesBelow x).length : Rat) / (M : Rat) := by
  rw [ordinaryPrimeWeightSum_eq]
  exact ordinary_primeList_allowance _ (ordinary_prefix_nodup x)
    (fun p hp => (PrimeFactorUnimodality.primesBelow_entries x p hp).1) M hM

end PrimeFactorOscillations
