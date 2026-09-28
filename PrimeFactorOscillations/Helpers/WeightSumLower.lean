import PrimeFactorOscillations.Helpers.GenericOddMertens

set_option autoImplicit false

/-! # A uniform unconditional lower constant for both prime-weight sums -/

namespace PrimeFactorOscillations

/-- A fixed lower-error allowance, independent of cutoff and rank. -/
noncomputable def primeWeightLowerConstant : Real :=
  2 + |Mertens.M| + PrimeFactorUnimodality.mertensErrorConstant / Real.log 2

/-- The fixed allowance is nonnegative. -/
theorem primeWeightLowerConstant_nonneg : 0 <= primeWeightLowerConstant := by
  unfold primeWeightLowerConstant
  exact add_nonneg (add_nonneg (by norm_num) (abs_nonneg _))
    (div_nonneg PrimeFactorUnimodality.mertensErrorConstant_nonneg
      (le_of_lt (Real.log_pos (by norm_num : (1 : Real) < 2))))

/-- Uniform generic lower bound with the exact natural cutoff convention. -/
theorem genericOdd_weightSum_lower (n : Nat) (hn : 2 <= n) :
    Real.log (Real.log n) - primeWeightLowerConstant <=
      (genericOddPrimeWeightSum (n + 1) : Real) := by
  have hraw := (genericOdd_mertens_bounds n hn).1
  have hlog2 : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 <= Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have herror := div_le_div_of_nonneg_left
    PrimeFactorUnimodality.mertensErrorConstant_nonneg hlog2 hlog
  have hm := neg_abs_le Mertens.M
  unfold primeWeightLowerConstant
  linarith

/-- The ordinary lower bound uses the same constant via the proved transfer. -/
theorem ordinary_weightSum_lower (n : Nat) (hn : 2 <= n) :
    Real.log (Real.log n) - primeWeightLowerConstant <=
      (ordinaryPrimeWeightSum (n + 1) : Real) := by
  have hcompare : (genericOddPrimeWeightSum (n + 1) : Real) <=
      (ordinaryPrimeWeightSum (n + 1) : Real) := by
    exact_mod_cast sub_nonneg.mp (genericOdd_weightSum_transfer (n + 1)).1
  exact (genericOdd_weightSum_lower n hn).trans hcompare

end PrimeFactorOscillations
