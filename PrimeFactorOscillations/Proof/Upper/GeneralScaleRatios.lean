import PrimeFactorOscillations.Helpers.RatioBounds
import PrimeFactorOscillations.Helpers.ScaleParameters
import PrimeFactorOscillations.Helpers.WeightDenominator

set_option autoImplicit false

/-! # Uniform ratio bounds at an arbitrary positive logarithmic scale -/

namespace PrimeFactorOscillations

/-- The entire signed denominator gives every ratio constant 1/a on any
strictly later scale b>a. The prefix allowance and fixed cost are both retained. -/
theorem both_ratios_eventually_below_of_scale (a b : Real)
    (ha : 0 < a) (hab : a < b) :
    exists K : Nat, 2 <= K /\ forall k : Nat, K <= k ->
      forall n : Nat, 2 <= n -> b * k <= Real.log (Real.log n) ->
      ((finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 2) /
        finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) : Rat) : Real) <= 1 / a /\
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) : Real) <= 1 / a /\
      k - 1 <= (oddPrimesBelow (n + 1)).length /\
      k - 1 <= (PrimeFactorUnimodality.primesBelow (n + 1)).length := by
  choose M hM using exists_upper_scale_parameters (4 * (b - a)) (by linarith)
  choose K hK using hM.2.2
  refine Exists.intro (max 2 K) (And.intro (le_max_left _ _) ?_)
  intro k hk n hn hscale
  have hkTwo : 2 <= k := (le_max_left 2 K).trans hk
  have hkR : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hcost := hK.2 k ((le_max_right 2 K).trans hk)
  have hsmall := mul_le_mul_of_nonneg_right hM.2.1 (Nat.cast_nonneg k : (0 : Real) <= k)
  have hquot : (k : Real) / M <= (4 * (b - a) / 8) * k := by
    simpa [div_eq_mul_inv, mul_comm] using hsmall
  have hrawG := genericOdd_denominator_lower n k M hn hM.1
  have hrawO := ordinary_denominator_lower n k M hn hM.1
  have hdenG : a * k <=
      ((genericOddPrimeWeightSum (n + 1) -
        (((oddPrimesBelow (n + 1)).map genericOddWeight).take (k - 2)).sum : Rat) : Real) := by
    nlinarith only [hrawG, hcost, hquot, hscale]
  have hdenO : a * k <=
      ((ordinaryPrimeWeightSum (n + 1) -
        (((PrimeFactorUnimodality.primesBelow (n + 1)).map
          PrimeFactorUnimodality.primeWeight).take (k - 2)).sum : Rat) : Real) := by
    nlinarith only [hrawO, hcost, hquot, hscale]
  have hposG := (mul_pos ha hkR).trans_le hdenG
  have hposO := (mul_pos ha hkR).trans_le hdenO
  exact And.intro (genericOdd_ratio_le_of_denominator (n + 1) k a hkTwo ha hdenG)
    (And.intro (ordinary_ratio_le_of_denominator (n + 1) k a hkTwo ha hdenO)
      (And.intro
        (genericOdd_degree_supported_of_complement_pos (n + 1) k
          ((Rat.cast_pos (K := Real)).mp hposG))
        (ordinary_degree_supported_of_complement_pos (n + 1) k
          ((Rat.cast_pos (K := Real)).mp hposO))))

end PrimeFactorOscillations
