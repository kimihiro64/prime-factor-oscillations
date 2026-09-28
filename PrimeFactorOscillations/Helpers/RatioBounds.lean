import PrimeFactorOscillations.Helpers.PrefixSupport

set_option autoImplicit false

/-! # Both actual density ratios from a positive linear denominator bound -/

namespace PrimeFactorOscillations

/-- Generic odd ratio with the degree support and all division signs discharged. -/
theorem genericOdd_ratio_le_of_denominator (x k : Nat) (a : Real)
    (hk : 2 <= k) (ha : 0 < a)
    (hD : a * k <= ((genericOddPrimeWeightSum x -
      (((oddPrimesBelow x).map genericOddWeight).take (k - 2)).sum : Rat) : Real)) :
    ((finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow x) (k - 2) /
      finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow x) (k - 1) : Rat) : Real) <=
        1 / a := by
  have hkR : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hprod := mul_pos ha hkR
  have hpositive := hprod.trans_le hD
  have hRatPositive := (Rat.cast_pos (K := Real)).mp hpositive
  have hsupport := genericOdd_degree_supported_of_complement_pos x k hRatPositive
  have hsub : k - 1 - 1 = k - 2 := by omega
  have hc : 0 < genericOddPrimeWeightSum x -
      (((oddPrimesBelow x).map genericOddWeight).take (k - 1 - 1)).sum := by
    simpa only [hsub] using hRatPositive
  have hq := (genericOdd_prefix_ratio_bounds x (k - 1) (by omega) hsupport hc).2
  rw [hsub] at hq
  have hreal := (Rat.cast_le (K := Real)).mpr hq
  simp only [Rat.cast_div, Rat.cast_natCast] at hreal
  have hnum : ((k - 1 : Nat) : Real) <= (k : Real) := by exact_mod_cast Nat.sub_le k 1
  have hfirst := div_le_div_of_nonneg_right hnum hpositive.le
  have hsecond := div_le_div_of_nonneg_left (Nat.cast_nonneg k : (0 : Real) <= k) hprod hD
  have hcancel : (k : Real) / (a * k) = 1 / a := by
    simpa only [one_mul] using mul_div_mul_right (1 : Real) a (ne_of_gt hkR)
  rw [Rat.cast_div]
  exact hreal.trans (hfirst.trans (hsecond.trans_eq hcancel))

/-- Ordinary ratio using the proved symmetric bound in the pinned dependency. -/
theorem ordinary_ratio_le_of_denominator (x k : Nat) (a : Real)
    (hk : 2 <= k) (ha : 0 < a)
    (hD : a * k <= ((ordinaryPrimeWeightSum x -
      (((PrimeFactorUnimodality.primesBelow x).map
        PrimeFactorUnimodality.primeWeight).take (k - 2)).sum : Rat) : Real)) :
    (PrimeFactorUnimodality.densityRatio
      (PrimeFactorUnimodality.primesBelow x) (k - 1) : Real) <= 1 / a := by
  have hkR : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hprod := mul_pos ha hkR
  have hpositive := hprod.trans_le hD
  have hRatPositive := (Rat.cast_pos (K := Real)).mp hpositive
  have hsupport := ordinary_degree_supported_of_complement_pos x k hRatPositive
  have hsub : k - 1 - 1 = k - 2 := by omega
  have hc : 0 < PrimeFactorUnimodality.weightSum (PrimeFactorUnimodality.primesBelow x) -
      PrimeFactorUnimodality.leadingWeightSum
        (PrimeFactorUnimodality.primesBelow x) (k - 1 - 1) := by
    simpa only [ordinaryPrimeWeightSum_eq,
      PrimeFactorUnimodality.leadingWeightSum_eq_weightSum_take,
      PrimeFactorUnimodality.weightSum, List.map_take, hsub] using hRatPositive
  have hraw := PrimeFactorUnimodality.densityRatio_le_degree_div_weightSum_sub_leading
    (PrimeFactorUnimodality.primesBelow x) (PrimeFactorUnimodality.primesBelow_gt_one x)
    (PrimeFactorUnimodality.primesBelow_weights_descending x)
    (k - 1) (by omega) hsupport hc
  have hq : PrimeFactorUnimodality.densityRatio (PrimeFactorUnimodality.primesBelow x) (k - 1) <=
      ((k - 1 : Nat) : Rat) / (ordinaryPrimeWeightSum x -
        (((PrimeFactorUnimodality.primesBelow x).map
          PrimeFactorUnimodality.primeWeight).take (k - 2)).sum) := by
    simpa only [ordinaryPrimeWeightSum_eq,
      PrimeFactorUnimodality.leadingWeightSum_eq_weightSum_take,
      PrimeFactorUnimodality.weightSum, List.map_take, hsub] using hraw
  have hreal := (Rat.cast_le (K := Real)).mpr hq
  simp only [Rat.cast_div, Rat.cast_natCast] at hreal
  have hnum : ((k - 1 : Nat) : Real) <= (k : Real) := by exact_mod_cast Nat.sub_le k 1
  have hfirst := div_le_div_of_nonneg_right hnum hpositive.le
  have hsecond := div_le_div_of_nonneg_left (Nat.cast_nonneg k : (0 : Real) <= k) hprod hD
  have hcancel : (k : Real) / (a * k) = 1 / a := by
    simpa only [one_mul] using mul_div_mul_right (1 : Real) a (ne_of_gt hkR)
  exact hreal.trans (hfirst.trans (hsecond.trans_eq hcancel))

end PrimeFactorOscillations
