import PrimeFactorUnimodality.Helpers.FirstDifference.PrimeSequence

/-! # No omitted prime between consecutive canonical prime indices -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- The dependency's consecutive enumeration omits no intermediate prime. -/
theorem no_prime_between_consecutive_indexed (i t : Nat)
    (hlo : PrimeFactorUnimodality.primeAt i < t)
    (hhi : t < PrimeFactorUnimodality.primeAt (i + 1)) :
    Not (Nat.Prime t) := by
  intro ht
  have hm : List.Mem t
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt (i + 1))) := by
    unfold PrimeFactorUnimodality.primesBelow
    exact (Finset.mem_sort (r := fun a b : Nat => a <= b)).mpr
      (Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr hhi) ht))
  have hmem := (PrimeFactorUnimodality.primesBelow_primeAt_succ_perm i).mem_iff.mp hm
  have hc : t = PrimeFactorUnimodality.primeAt i \/
      (t < PrimeFactorUnimodality.primeAt i /\ Nat.Prime t) := by
    simpa [PrimeFactorUnimodality.primesBelow] using hmem
  rcases hc with heq | hsmall
  next => omega
  next => omega


end PrimeFactorOscillations
