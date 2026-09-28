import PrimeFactorOscillations.Proof.Lower.ScaleRatios

/-! # Sharp uniform density ratios on additive rank bands -/

namespace PrimeFactorOscillations

private theorem threshold_lt_ratio_of_sum_bound {T b C S R : Real} {k : Nat}
    (hT : 0 < T) (hk : 1 <= k) (hS : 0 < S)
    (hsum : S <= b * k + C)
    (hbudget : T * C + 1 < (1 - T * b) * k)
    (hratio : ((k - 1 : Nat) : Real) / S <= R) : T < R := by
  have hmul := mul_le_mul_of_nonneg_left hsum hT.le
  have hnum : T * S < ((k - 1 : Nat) : Real) := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    nlinarith only [hmul, hbudget]
  have hcancel : (((k - 1 : Nat) : Real) / S) * S = ((k - 1 : Nat) : Real) := by
    field_simp [ne_of_gt hS]
  have hlower : T < ((k - 1 : Nat) : Real) / S := by
    nlinarith only [hnum, hcancel, hS]
  exact hlower.trans_le hratio

/-- The actual two density ratios on an additive log-log band, retaining the
full signed denominator bound and the required degree supports. -/
theorem both_ratios_eventually_in_additive_band (T b : Real)
    (hT : 0 < T) (hb : 0 < b) (hmargin : T * b < 1) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k -> forall n : Nat, 2 <= n ->
      b * k - Real.log 2 <= Real.log (Real.log n) ->
      Real.log (Real.log n) <= b * k + Real.log 2 ->
      T <
        ((finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 2) /
          finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) :
            Rat) : Real) /\
      ((finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 2) /
          finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) :
            Rat) : Real) <= 1 / (((2 : Real) / 3) * b) /\
      T < (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) : Real) /\
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) : Real) <=
          1 / (((2 : Real) / 3) * b) /\
      k - 1 <= (oddPrimesBelow (n + 1)).length /\
      k - 1 <= (PrimeFactorUnimodality.primesBelow (n + 1)).length := by
  let C := Real.log 2 + primeWeightLowerConstant
  choose Kw hKw using both_weight_estimates_eventually_in_band b hb
  choose Kt hKt using exists_nat_gt
    (max (4 * Real.log 2 / b) ((T * C + 1) / (1 - T * b)))
  refine Exists.intro (max Kw Kt) (And.intro (hKw.1.trans (le_max_left _ _)) ?_)
  intro k hk n hn hlow hhigh
  have hkw : Kw <= k := (le_max_left _ _).trans hk
  have hkt : Kt <= k := (le_max_right _ _).trans hk
  have hkk : (Kt : Real) <= k := by exact_mod_cast hkt
  have hlogscale : 4 * Real.log 2 / b < (k : Real) :=
    ((le_max_left _ _).trans_lt hKt).trans_le hkk
  have hscaled : 4 * Real.log 2 < (k : Real) * b := by
    have h := mul_lt_mul_of_pos_right hlogscale hb
    have hc : (4 * Real.log 2 / b) * b = 4 * Real.log 2 := by
      field_simp [ne_of_gt hb]
    rwa [hc] at h
  have hbandLow : ((3 : Real) / 4) * b * k <= Real.log (Real.log n) := by
    nlinarith only [hlow, hscaled]
  have hbandHigh : Real.log (Real.log n) <= ((5 : Real) / 4) * b * k := by
    nlinarith only [hhigh, hscaled]
  have hbudgetRatio : (T * C + 1) / (1 - T * b) < (k : Real) :=
    ((le_max_right _ _).trans_lt hKt).trans_le hkk
  have hbudget : T * C + 1 < (1 - T * b) * k := by
    have h := mul_lt_mul_of_pos_right hbudgetRatio (sub_pos.mpr hmargin)
    have hc : ((T * C + 1) / (1 - T * b)) * (1 - T * b) = T * C + 1 := by
      field_simp [ne_of_gt (sub_pos.mpr hmargin)]
    rw [hc] at h
    nlinarith only [h]
  have hw := hKw.2 k hkw n hn hbandLow hbandHigh
  have hupper := both_primeWeightSums_upper n hn
  have hsumG : (genericOddPrimeWeightSum (n + 1) : Real) <= b * k + C := by
    dsimp [C]
    linarith only [hupper.1, hhigh]
  have hsumO : (ordinaryPrimeWeightSum (n + 1) : Real) <= b * k + C := by
    dsimp [C]
    linarith only [hupper.2, hhigh]
  have hk4 : 4 <= k := hKw.1.trans hkw
  have hk0 : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have ha : (0 : Real) < ((2 : Real) / 3) * b := by positivity
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
  have hsumOpos : 0 < PrimeFactorUnimodality.weightSum
      (PrimeFactorUnimodality.primesBelow (n + 1)) := by
    rw [<- ordinaryPrimeWeightSum_eq]
    exact (Rat.cast_pos (K := Real)).mp hw.2.2.2.2.2
  have hrawO := PrimeFactorUnimodality.degree_div_weightSum_le_densityRatio
    (PrimeFactorUnimodality.primesBelow (n + 1))
    (PrimeFactorUnimodality.primesBelow_gt_one (n + 1)) (k - 1) hsO hsumOpos
  rw [<- ordinaryPrimeWeightSum_eq] at hrawO
  have hrealO := (Rat.cast_le (K := Real)).mpr hrawO
  simp only [Rat.cast_div, Rat.cast_natCast] at hrealO
  have hlG := threshold_lt_ratio_of_sum_bound hT (by omega)
    hw.2.2.2.2.1 hsumG hbudget hrealG
  have hlO := threshold_lt_ratio_of_sum_bound hT (by omega)
    hw.2.2.2.2.2 hsumO hbudget hrealO
  have huG := genericOdd_ratio_le_of_denominator (n + 1) k _ (by omega) ha hw.1
  have huO := ordinary_ratio_le_of_denominator (n + 1) k _ (by omega) ha hw.2.1
  simpa only [Rat.cast_div] using
    And.intro hlG (And.intro huG (And.intro hlO
      (And.intro huO (And.intro hsG hsO))))

end PrimeFactorOscillations
