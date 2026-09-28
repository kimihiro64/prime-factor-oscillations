import PrimeFactorOscillations.Helpers.ScaleParameters
import PrimeFactorOscillations.Helpers.WeightDenominator
import PrimeFactorOscillations.Helpers.WeightSumUpper

/-! # Signed weight estimates with all lower-band allowances retained -/

namespace PrimeFactorOscillations

/-- Uniform actual sums and signed denominators on a rank-dependent log-log band. -/
theorem both_weight_estimates_eventually_in_band (beta : Real) (hb : 0 < beta) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k -> forall n : Nat, 2 <= n ->
      ((3 : Real) / 4) * beta * k <= Real.log (Real.log n) ->
      Real.log (Real.log n) <= ((5 : Real) / 4) * beta * k ->
      ((2 : Real) / 3) * beta * k <=
        ((genericOddPrimeWeightSum (n + 1) -
          (((oddPrimesBelow (n + 1)).map genericOddWeight).take (k - 2)).sum : Rat) : Real) /\
      ((2 : Real) / 3) * beta * k <=
        ((ordinaryPrimeWeightSum (n + 1) -
          (((PrimeFactorUnimodality.primesBelow (n + 1)).map
            PrimeFactorUnimodality.primeWeight).take (k - 2)).sum : Rat) : Real) /\
      (genericOddPrimeWeightSum (n + 1) : Real) <= ((4 : Real) / 3) * beta * k /\
      (ordinaryPrimeWeightSum (n + 1) : Real) <= ((4 : Real) / 3) * beta * k /\
      0 < (genericOddPrimeWeightSum (n + 1) : Real) /\
      0 < (ordinaryPrimeWeightSum (n + 1) : Real) := by
  choose M hM using exists_upper_scale_parameters (beta / 3) (by positivity)
  choose K hK using hM.2.2
  refine Exists.intro (max 4 K) (And.intro (le_max_left _ _) ?_)
  intro k hk n hn hlow hhigh
  have hk4 : 4 <= k := (le_max_left 4 K).trans hk
  have hconstant := hK.2 k ((le_max_right 4 K).trans hk)
  have hcost : primeWeightLowerConstant + M + 1 <= (beta / 24) * k := by
    nlinarith only [hconstant]
  have hsmall : (1 : Real) / M <= beta / 24 := by nlinarith only [hM.2.1]
  have hscaled := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg k : (0 : Real) <= k)
  have hdivision : (k : Real) / M <= (beta / 24) * k := by
    simpa [div_eq_mul_inv, mul_comm] using hscaled
  have hgeneric := genericOdd_denominator_lower n k M hn hM.1
  have hordinary := ordinary_denominator_lower n k M hn hM.1
  have hupper := both_primeWeightSums_upper n hn
  have hlowerG := genericOdd_weightSum_lower n hn
  have hlowerO := ordinary_weightSum_lower n hn
  have hM0 : (0 : Real) <= M := Nat.cast_nonneg M
  have hk0 : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hbk : 0 < beta * k := mul_pos hb hk0
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))
  next => nlinarith only [hgeneric, hlow, hcost, hdivision]
  next => nlinarith only [hordinary, hlow, hcost, hdivision]
  next => nlinarith only [hupper.1, hhigh, hcost, hM0, hbk]
  next => nlinarith only [hupper.2, hhigh, hcost, hM0, hbk]
  next => nlinarith only [hlowerG, hlow, hcost, hM0, hbk]
  next => nlinarith only [hlowerO, hlow, hcost, hM0, hbk]

end PrimeFactorOscillations
