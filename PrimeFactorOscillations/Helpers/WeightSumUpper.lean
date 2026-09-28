import PrimeFactorOscillations.Helpers.WeightSumLower

set_option autoImplicit false

/-! # Uniform upper bounds for both canonical prime-weight sums -/

namespace PrimeFactorOscillations

/-- The existing fixed lower-error allowance also bounds both sums from above. -/
theorem both_primeWeightSums_upper (n : Nat) (hn : 2 <= n) :
    (genericOddPrimeWeightSum (n + 1) : Real) <=
      Real.log (Real.log n) + primeWeightLowerConstant /\
    (ordinaryPrimeWeightSum (n + 1) : Real) <=
      Real.log (Real.log n) + primeWeightLowerConstant := by
  have hraw := PrimeFactorUnimodality.primeWeightSumBelow_upper_of_estimate
    PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate hn
  have hlog2 : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 <= Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have herror := div_le_div_of_nonneg_left
    PrimeFactorUnimodality.mertensErrorConstant_nonneg hlog2 hlog
  have hm := le_abs_self Mertens.M
  have hordinary : (ordinaryPrimeWeightSum (n + 1) : Real) <=
      Real.log (Real.log n) + primeWeightLowerConstant := by
    rw [ratCast_ordinaryPrimeWeightSum]
    unfold primeWeightLowerConstant
    linarith
  have htransfer := (real_genericOdd_weightSum_transfer (n + 1)).1
  rw [<- ratCast_ordinaryPrimeWeightSum] at htransfer
  exact And.intro (by linarith) hordinary

end PrimeFactorOscillations
