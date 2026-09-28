import PrimeFactorOscillations.Proof.Upper.ScaleParameters
import PrimeFactorOscillations.Proof.Upper.WeightDenominator

set_option autoImplicit false

/-! # Uniform positive denominators at the double-exponential scale -/

namespace PrimeFactorOscillations

/-- All auxiliary finite choices are discharged before the rank and cutoff vary. -/
theorem both_denominators_eventually_at_scale (epsilon : Real) (he : 0 < epsilon) :
    exists K : Nat, 1 <= K /\ forall k : Nat, K <= k ->
      forall n : Nat, 2 <= n ->
      ((1 : Real) / 3 + epsilon / 2) * k <= Real.log (Real.log n) ->
      (((1 : Real) / 3 + epsilon / 4) * k <=
          ((genericOddPrimeWeightSum (n + 1) -
            (((oddPrimesBelow (n + 1)).map genericOddWeight).take (k - 2)).sum : Rat) : Real) /\
        0 < ((genericOddPrimeWeightSum (n + 1) -
          (((oddPrimesBelow (n + 1)).map genericOddWeight).take (k - 2)).sum : Rat) : Real)) /\
      (((1 : Real) / 3 + epsilon / 4) * k <=
          ((ordinaryPrimeWeightSum (n + 1) -
            (((PrimeFactorUnimodality.primesBelow (n + 1)).map
              PrimeFactorUnimodality.primeWeight).take (k - 2)).sum : Rat) : Real) /\
        0 < ((ordinaryPrimeWeightSum (n + 1) -
          (((PrimeFactorUnimodality.primesBelow (n + 1)).map
            PrimeFactorUnimodality.primeWeight).take (k - 2)).sum : Rat) : Real)) := by
  choose M hM using exists_upper_scale_parameters epsilon he
  choose K hK using hM.2.2
  refine Exists.intro K (And.intro hK.1 ?_)
  intro k hk n hn hscale
  have hkpos : 0 < k := by have hKone := hK.1; omega
  exact And.intro
    (genericOdd_denominator_at_scale n k M epsilon hn hkpos hM.1 he hscale
      hM.2.1 (hK.2 k hk))
    (ordinary_denominator_at_scale n k M epsilon hn hkpos hM.1 he hscale
      hM.2.1 (hK.2 k hk))

end PrimeFactorOscillations
