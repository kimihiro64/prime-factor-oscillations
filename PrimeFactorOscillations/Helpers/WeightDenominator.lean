import PrimeFactorOscillations.Helpers.PrefixAllowance
import PrimeFactorOscillations.Helpers.WeightSumLower

set_option autoImplicit false

/-!
# The complete signed lower bound for the ratio denominator

The positive Mertens contribution and the entire removed-prefix allowance
are combined before any scale choice. Every bound is uniform in the cutoff
and rank; the finite parameters used to absorb the errors remain explicit.
-/

namespace PrimeFactorOscillations

/-- The generic denominator with every negative allowance retained. -/
theorem genericOdd_denominator_lower (n k M : Nat) (hn : 2 <= n) (hM : 0 < M) :
    Real.log (Real.log n) - primeWeightLowerConstant - ((M : Real) + 1) -
        (k : Real) / (M : Real) <=
      ((genericOddPrimeWeightSum (n + 1) -
        (((oddPrimesBelow (n + 1)).map genericOddWeight).take (k - 2)).sum : Rat) : Real) := by
  have hs := genericOdd_weightSum_lower n hn
  have hp :
      ((((oddPrimesBelow (n + 1)).map genericOddWeight).take (k - 2)).sum : Real) <=
        (M : Real) + 1 + ((k - 2 : Nat) : Real) / (M : Real) := by
    have hcast := (Rat.cast_le (K := Real)).2
      (genericOdd_prefix_allowance (n + 1) (k - 2) M hM)
    simpa only [Rat.cast_add, Rat.cast_one, Rat.cast_div, Rat.cast_natCast] using hcast
  have hk : ((k - 2 : Nat) : Real) <= (k : Real) := by
    exact_mod_cast Nat.sub_le k 2
  have hd := div_le_div_of_nonneg_right hk (Nat.cast_nonneg M : (0 : Real) <= M)
  rw [Rat.cast_sub]
  linarith

/-- The same full signed bound for the ordinary denominator. -/
theorem ordinary_denominator_lower (n k M : Nat) (hn : 2 <= n) (hM : 0 < M) :
    Real.log (Real.log n) - primeWeightLowerConstant - ((M : Real) + 1) -
        (k : Real) / (M : Real) <=
      ((ordinaryPrimeWeightSum (n + 1) -
        (((PrimeFactorUnimodality.primesBelow (n + 1)).map
          PrimeFactorUnimodality.primeWeight).take (k - 2)).sum : Rat) : Real) := by
  have hs := ordinary_weightSum_lower n hn
  have hp :
      ((((PrimeFactorUnimodality.primesBelow (n + 1)).map
        PrimeFactorUnimodality.primeWeight).take (k - 2)).sum : Real) <=
          (M : Real) + 1 + ((k - 2 : Nat) : Real) / (M : Real) := by
    have hcast := (Rat.cast_le (K := Real)).2
      (ordinary_prefix_allowance (n + 1) (k - 2) M hM)
    simpa only [Rat.cast_add, Rat.cast_one, Rat.cast_div, Rat.cast_natCast] using hcast
  have hk : ((k - 2 : Nat) : Real) <= (k : Real) := by
    exact_mod_cast Nat.sub_le k 2
  have hd := div_le_div_of_nonneg_right hk (Nat.cast_nonneg M : (0 : Real) <= M)
  rw [Rat.cast_sub]
  linarith

/-- The desired positive leading coefficient follows from explicit scale and
fixed-parameter inequalities, with no additional prime-distribution assumption. -/
theorem genericOdd_denominator_at_scale (n k M : Nat) (epsilon : Real)
    (hn : 2 <= n) (hk : 0 < k) (hM : 0 < M) (he : 0 < epsilon)
    (hscale : ((1 : Real) / 3 + epsilon / 2) * k <= Real.log (Real.log n))
    (hsmall : (1 : Real) / M <= epsilon / 8)
    (hconstant : primeWeightLowerConstant + M + 1 <= (epsilon / 8) * k) :
    ((1 : Real) / 3 + epsilon / 4) * k <=
        ((genericOddPrimeWeightSum (n + 1) -
          (((oddPrimesBelow (n + 1)).map genericOddWeight).take (k - 2)).sum : Rat) : Real) /\
      0 < ((genericOddPrimeWeightSum (n + 1) -
        (((oddPrimesBelow (n + 1)).map genericOddWeight).take (k - 2)).sum : Rat) : Real) := by
  have hraw := genericOdd_denominator_lower n k M hn hM
  have hscaled := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg k : (0 : Real) <= k)
  have hdivision : (k : Real) / M <= (epsilon / 8) * k := by
    simpa [div_eq_mul_inv, mul_comm] using hscaled
  have hbound : ((1 : Real) / 3 + epsilon / 4) * k <=
      ((genericOddPrimeWeightSum (n + 1) -
        (((oddPrimesBelow (n + 1)).map genericOddWeight).take (k - 2)).sum : Rat) : Real) := by
    nlinarith only [hraw, hscale, hconstant, hdivision]
  exact And.intro hbound
    ((mul_pos (by linarith : (0 : Real) < 1 / 3 + epsilon / 4)
      (by exact_mod_cast hk : (0 : Real) < k)).trans_le hbound)

/-- The identical positive leading coefficient for the ordinary family. -/
theorem ordinary_denominator_at_scale (n k M : Nat) (epsilon : Real)
    (hn : 2 <= n) (hk : 0 < k) (hM : 0 < M) (he : 0 < epsilon)
    (hscale : ((1 : Real) / 3 + epsilon / 2) * k <= Real.log (Real.log n))
    (hsmall : (1 : Real) / M <= epsilon / 8)
    (hconstant : primeWeightLowerConstant + M + 1 <= (epsilon / 8) * k) :
    ((1 : Real) / 3 + epsilon / 4) * k <=
        ((ordinaryPrimeWeightSum (n + 1) -
          (((PrimeFactorUnimodality.primesBelow (n + 1)).map
            PrimeFactorUnimodality.primeWeight).take (k - 2)).sum : Rat) : Real) /\
      0 < ((ordinaryPrimeWeightSum (n + 1) -
        (((PrimeFactorUnimodality.primesBelow (n + 1)).map
          PrimeFactorUnimodality.primeWeight).take (k - 2)).sum : Rat) : Real) := by
  have hraw := ordinary_denominator_lower n k M hn hM
  have hscaled := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg k : (0 : Real) <= k)
  have hdivision : (k : Real) / M <= (epsilon / 8) * k := by
    simpa [div_eq_mul_inv, mul_comm] using hscaled
  have hbound : ((1 : Real) / 3 + epsilon / 4) * k <=
      ((ordinaryPrimeWeightSum (n + 1) -
        (((PrimeFactorUnimodality.primesBelow (n + 1)).map
          PrimeFactorUnimodality.primeWeight).take (k - 2)).sum : Rat) : Real) := by
    nlinarith only [hraw, hscale, hconstant, hdivision]
  exact And.intro hbound
    ((mul_pos (by linarith : (0 : Real) < 1 / 3 + epsilon / 4)
      (by exact_mod_cast hk : (0 : Real) < k)).trans_le hbound)

end PrimeFactorOscillations
