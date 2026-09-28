import PrimeFactorOscillations.Helpers.GenericOddPrefix

set_option autoImplicit false

/-! # A positive complement ensures the density degree is supported -/

namespace PrimeFactorOscillations

/-- If the generic complement is positive, its degree is supported. The proof
uses exact prefix exhaustion, not an independent prime-counting estimate. -/
theorem genericOdd_degree_supported_of_complement_pos (x k : Nat)
    (hD : 0 < genericOddPrimeWeightSum x -
      (((oddPrimesBelow x).map genericOddWeight).take (k - 2)).sum) :
    k - 1 <= (oddPrimesBelow x).length := by
  by_contra hnot
  have hlen : (oddPrimesBelow x).length <= k - 2 := by omega
  have ht : (((oddPrimesBelow x).map genericOddWeight).take (k - 2)) =
      (oddPrimesBelow x).map genericOddWeight :=
    List.take_of_length_le (by simpa only [List.length_map] using hlen)
  rw [ht, genericOdd_sum_oddPrimesBelow, sub_self] at hD
  exact (lt_irrefl (0 : Rat)) hD

/-- The ordinary degree follows from the same exact complement argument. -/
theorem ordinary_degree_supported_of_complement_pos (x k : Nat)
    (hD : 0 < ordinaryPrimeWeightSum x -
      (((PrimeFactorUnimodality.primesBelow x).map
        PrimeFactorUnimodality.primeWeight).take (k - 2)).sum) :
    k - 1 <= (PrimeFactorUnimodality.primesBelow x).length := by
  by_contra hnot
  have hlen : (PrimeFactorUnimodality.primesBelow x).length <= k - 2 := by omega
  have ht : (((PrimeFactorUnimodality.primesBelow x).map
      PrimeFactorUnimodality.primeWeight).take (k - 2)) =
        (PrimeFactorUnimodality.primesBelow x).map PrimeFactorUnimodality.primeWeight :=
    List.take_of_length_le (by simpa only [List.length_map] using hlen)
  rw [ht, ordinaryPrimeWeightSum_eq, PrimeFactorUnimodality.weightSum, sub_self] at hD
  exact (lt_irrefl (0 : Rat)) hD

end PrimeFactorOscillations
