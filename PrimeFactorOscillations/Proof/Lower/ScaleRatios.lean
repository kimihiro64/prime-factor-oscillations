import PrimeFactorOscillations.Helpers.RatioBounds
import PrimeFactorOscillations.Proof.Lower.ScaleWeights

/-! # Both density ratios uniformly on the lower logarithmic band -/

namespace PrimeFactorOscillations

private theorem ratio_lower_of_band {beta S R : Real} {k : Nat}
    (hb : 0 < beta) (hk : 4 <= k) (hS : 0 < S)
    (hupper : S <= ((4 : Real) / 3) * beta * k)
    (hratio : ((k - 1 : Nat) : Real) / S <= R) :
    1 / (2 * beta) < R := by
  have hmult := mul_le_mul_of_nonneg_left hupper
    (le_of_lt (one_div_pos.mpr (show (0 : Real) < 2 * beta by positivity)))
  have heq : (1 / (2 * beta)) * (((4 : Real) / 3) * beta * k) =
      ((2 : Real) / 3) * k := by
    field_simp [ne_of_gt hb]
    ring
  rw [heq] at hmult
  have hnum : (1 / (2 * beta)) * S < ((k - 1 : Nat) : Real) := by
    rw [Nat.cast_sub (by omega : 1 <= k), Nat.cast_one]
    have hkR : (4 : Real) <= k := by exact_mod_cast hk
    linarith
  have hcancel : (((k - 1 : Nat) : Real) / S) * S = ((k - 1 : Nat) : Real) := by
    field_simp [ne_of_gt hS]
  apply lt_of_lt_of_le _ hratio
  nlinarith only [hnum, hcancel, hS]

/-- Both actual density ratios are bounded above and below uniformly in the band. -/
theorem both_ratios_eventually_in_lower_band (beta : Real) (hb : 0 < beta) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k -> forall n : Nat, 2 <= n ->
      ((3 : Real) / 4) * beta * k <= Real.log (Real.log n) ->
      Real.log (Real.log n) <= ((5 : Real) / 4) * beta * k ->
      1 / (2 * beta) <
        ((finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 2) /
          finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) :
            Rat) : Real) /\
      ((finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 2) /
          finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) :
            Rat) : Real) <= 1 / (((2 : Real) / 3) * beta) /\
      1 / (2 * beta) < (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) : Real) /\
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) : Real) <=
          1 / (((2 : Real) / 3) * beta) /\
      k - 1 <= (oddPrimesBelow (n + 1)).length /\
      k - 1 <= (PrimeFactorUnimodality.primesBelow (n + 1)).length := by
  choose K hK using both_weight_estimates_eventually_in_band beta hb
  refine Exists.intro K (And.intro hK.1 ?_)
  intro k hk n hn hlow hhigh
  have hk4 : 4 <= k := hK.1.trans hk
  have hw := hK.2 k hk n hn hlow hhigh
  have hk0 : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have ha : (0 : Real) < ((2 : Real) / 3) * beta := by positivity
  have hpos := mul_pos ha hk0
  have hDG := hpos.trans_le hw.1
  have hDO := hpos.trans_le hw.2.1
  have hDGRat := (Rat.cast_pos (K := Real)).mp hDG
  have hDORat := (Rat.cast_pos (K := Real)).mp hDO
  have hsG := genericOdd_degree_supported_of_complement_pos (n + 1) k hDGRat
  have hsO := ordinary_degree_supported_of_complement_pos (n + 1) k hDORat
  have hsub : k - 1 - 1 = k - 2 := by omega
  have hcomp : 0 < genericOddPrimeWeightSum (n + 1) -
      (((oddPrimesBelow (n + 1)).map genericOddWeight).take (k - 1 - 1)).sum := by
    simpa only [hsub] using hDGRat
  have hrawG := (genericOdd_prefix_ratio_bounds (n + 1) (k - 1) (by omega) hsG hcomp).1
  have hrealG := (Rat.cast_le (K := Real)).mpr hrawG
  simp only [Rat.cast_div, Rat.cast_natCast, hsub] at hrealG
  have hsumO : 0 < PrimeFactorUnimodality.weightSum
      (PrimeFactorUnimodality.primesBelow (n + 1)) := by
    rw [<- ordinaryPrimeWeightSum_eq]
    exact (Rat.cast_pos (K := Real)).mp hw.2.2.2.2.2
  have hrawO := PrimeFactorUnimodality.degree_div_weightSum_le_densityRatio
    (PrimeFactorUnimodality.primesBelow (n + 1))
    (PrimeFactorUnimodality.primesBelow_gt_one (n + 1)) (k - 1) hsO hsumO
  rw [<- ordinaryPrimeWeightSum_eq] at hrawO
  have hrealO := (Rat.cast_le (K := Real)).mpr hrawO
  simp only [Rat.cast_div, Rat.cast_natCast] at hrealO
  have hlG := ratio_lower_of_band hb hk4 hw.2.2.2.2.1 hw.2.2.1 hrealG
  have hlO := ratio_lower_of_band hb hk4 hw.2.2.2.2.2 hw.2.2.2.1 hrealO
  have huG := genericOdd_ratio_le_of_denominator (n + 1) k _ (by omega) ha hw.1
  have huO := ordinary_ratio_le_of_denominator (n + 1) k _ (by omega) ha hw.2.1
  simpa only [Rat.cast_div] using
    And.intro hlG (And.intro huG (And.intro hlO
      (And.intro huO (And.intro hsG hsO))))

end PrimeFactorOscillations
