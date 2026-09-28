import PrimeFactorOscillations.Helpers.PrimePrefixWeights
import PrimeFactorUnimodality.Helpers.Analytic.MertensProvider

set_option autoImplicit false

/-!
# Unconditional logarithmic bounds for the generic odd weight sum

The analytic provider is the proved Mertens theorem in the pinned dependency,
not its conditional sharper theta-error input. The finite prime-two correction
and all later weight corrections are included explicitly.
-/

namespace PrimeFactorOscillations

/-- An explicit two-sided Mertens estimate for every natural cutoff at least two.
The additive constants are uniform in the cutoff and in the rank. -/
theorem genericOdd_mertens_bounds (n : Nat) (hn : 2 <= n) :
    Real.log (Real.log n) + Mertens.M -
        PrimeFactorUnimodality.mertensErrorConstant / Real.log n - 2 <=
        (genericOddPrimeWeightSum (n + 1) : Real) /\
      (genericOddPrimeWeightSum (n + 1) : Real) <=
        Real.log (Real.log n) + Mertens.M +
          PrimeFactorUnimodality.mertensErrorConstant / Real.log n + 1 := by
  have htransfer := real_genericOdd_weightSum_transfer (n + 1)
  have hlower := PrimeFactorUnimodality.reciprocalPrimeSumBelow_lower_of_estimate
    PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate hn
  have hcompare :=
    PrimeFactorUnimodality.reciprocalPrimeSumBelow_le_primeWeightSumBelow (n + 1)
  have hupper := PrimeFactorUnimodality.primeWeightSumBelow_upper_of_estimate
    PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate hn
  exact And.intro (by linarith [htransfer.2]) (by linarith [htransfer.1])

end PrimeFactorOscillations
