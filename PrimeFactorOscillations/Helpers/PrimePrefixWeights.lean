import PrimeFactorOscillations.Helpers.GenericOddWeightSums
import PrimeFactorUnimodality.Helpers.Analytic.PrimeWeightSum

set_option autoImplicit false

/-! # Canonical prime-prefix bridges for the weight estimates -/

namespace PrimeFactorOscillations

/-- Sorting the finite prime support does not change its weight sum. -/
theorem sum_primesBelow_eq (f : Nat -> Rat) (x : Nat) :
    ((PrimeFactorUnimodality.primesBelow x).map f).sum =
      ((Finset.range x).filter Nat.Prime).sum f := by
  change
    (Multiset.map f
      ((((Finset.range x).filter Nat.Prime).sort (fun a b => a <= b)) :
        Multiset Nat)).sum =
      (Multiset.map f ((Finset.range x).filter Nat.Prime).val).sum
  rw [Finset.sort_eq]

/-- Identify the ordinary finite-set sum with the dependency's canonical sum. -/
theorem ordinaryPrimeWeightSum_eq (x : Nat) :
    ordinaryPrimeWeightSum x =
      PrimeFactorUnimodality.weightSum (PrimeFactorUnimodality.primesBelow x) := by
  exact (sum_primesBelow_eq PrimeFactorUnimodality.primeWeight x).symm

/-- The same exact support bridge for the generic odd law. -/
theorem genericOddPrimeWeightSum_eq (x : Nat) :
    genericOddPrimeWeightSum x =
      ((PrimeFactorUnimodality.primesBelow x).map genericOddWeight).sum := by
  exact (sum_primesBelow_eq genericOddWeight x).symm

/-- Transport the ordinary sum to the real-valued analytic interface. -/
theorem ratCast_ordinaryPrimeWeightSum (x : Nat) :
    (ordinaryPrimeWeightSum x : Real) =
      PrimeFactorUnimodality.primeWeightSumBelow x := by
  rw [ordinaryPrimeWeightSum_eq,
    PrimeFactorUnimodality.ratCast_weightSum_primesBelow]

/-- Real-valued bounded-error transfer on the exact analytic cutoff. -/
theorem real_genericOdd_weightSum_transfer (x : Nat) :
    0 <= PrimeFactorUnimodality.primeWeightSumBelow x -
        (genericOddPrimeWeightSum x : Real) /\
      PrimeFactorUnimodality.primeWeightSumBelow x -
        (genericOddPrimeWeightSum x : Real) <= 2 := by
  rw [<- ratCast_ordinaryPrimeWeightSum]
  exact_mod_cast genericOdd_weightSum_transfer x

end PrimeFactorOscillations
