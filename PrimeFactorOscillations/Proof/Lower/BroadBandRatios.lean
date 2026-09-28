import PrimeFactorOscillations.Helpers.RatioBounds
import PrimeFactorOscillations.Helpers.ScaleParameters
import PrimeFactorOscillations.Helpers.WeightDenominator
import PrimeFactorOscillations.Helpers.WeightSumUpper

/-! # Uniform density ratios on broad logarithmic rank bands -/

set_option autoImplicit false

namespace PrimeFactorOscillations

private theorem broad_band_weight_estimates (u v : Real) (hu : 0 < u) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k -> forall n : Nat, 2 <= n ->
      u * k <= Real.log (Real.log n) ->
      Real.log (Real.log n) <= v * k ->
      (u / 2) * k <=
        ((genericOddPrimeWeightSum (n + 1) -
          (((oddPrimesBelow (n + 1)).map genericOddWeight).take (k - 2)).sum : Rat) : Real) /\
      (u / 2) * k <=
        ((ordinaryPrimeWeightSum (n + 1) -
          (((PrimeFactorUnimodality.primesBelow (n + 1)).map
            PrimeFactorUnimodality.primeWeight).take (k - 2)).sum : Rat) : Real) /\
      (genericOddPrimeWeightSum (n + 1) : Real) <= v * k + primeWeightLowerConstant /\
      (ordinaryPrimeWeightSum (n + 1) : Real) <= v * k + primeWeightLowerConstant /\
      0 < (genericOddPrimeWeightSum (n + 1) : Real) /\
      0 < (ordinaryPrimeWeightSum (n + 1) : Real) := by
  choose M hM using exists_upper_scale_parameters (2 * u) (by positivity)
  choose K hK using hM.2.2
  refine Exists.intro (max 4 K) (And.intro (le_max_left _ _) ?_)
  intro k hk n hn hlow hhigh
  have hcost : primeWeightLowerConstant + M + 1 <= (u / 4) * k := by
    have h := hK.2 k ((le_max_right 4 K).trans hk)
    nlinarith only [h]
  have hsmall : (1 : Real) / M <= u / 4 := by
    nlinarith only [hM.2.1]
  have hscaled := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg k : (0 : Real) <= k)
  have hdivision : (k : Real) / M <= (u / 4) * k := by
    simpa [div_eq_mul_inv, mul_comm] using hscaled
  have hgeneric := genericOdd_denominator_lower n k M hn hM.1
  have hordinary := ordinary_denominator_lower n k M hn hM.1
  have hupper := both_primeWeightSums_upper n hn
  have hlowerG := genericOdd_weightSum_lower n hn
  have hlowerO := ordinary_weightSum_lower n hn
  have hM0 : (0 : Real) <= M := Nat.cast_nonneg M
  have hk4 : 4 <= k := (le_max_left 4 K).trans hk
  have hk0 : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have huk : 0 < u * k := mul_pos hu hk0
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))
  next => nlinarith only [hgeneric, hlow, hcost, hdivision]
  next => nlinarith only [hordinary, hlow, hcost, hdivision]
  next => linarith only [hupper.1, hhigh]
  next => linarith only [hupper.2, hhigh]
  next => nlinarith only [hlowerG, hlow, hcost, hM0, huk]
  next => nlinarith only [hlowerO, hlow, hcost, hM0, huk]

/-- Every fixed broad band with T*v<1 has ratio above T and at most 2/u.
The lower endpoint pays only a fixed counting loss in the rate-characterization consumer. -/
theorem both_ratios_eventually_in_broad_band (T u v : Real)
    (hT : 0 < T) (hu : 0 < u) (hmargin : T * v < 1) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k -> forall n : Nat, 2 <= n ->
      u * k <= Real.log (Real.log n) ->
      Real.log (Real.log n) <= v * k ->
      T <
        ((finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 2) /
          finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) :
            Rat) : Real) /\
      ((finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 2) /
          finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) :
            Rat) : Real) <= 2 / u /\
      T < (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) : Real) /\
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) : Real) <= 2 / u /\
      k - 1 <= (oddPrimesBelow (n + 1)).length /\
      k - 1 <= (PrimeFactorUnimodality.primesBelow (n + 1)).length := by
  choose Kw hKw using broad_band_weight_estimates u v hu
  choose Kt hKt using exists_nat_gt
    ((T * primeWeightLowerConstant + 1) / (1 - T * v))
  refine Exists.intro (max Kw Kt) (And.intro (hKw.1.trans (le_max_left _ _)) ?_)
  intro k hk n hn hlow hhigh
  have hkw : Kw <= k := (le_max_left _ _).trans hk
  have hkt : Kt <= k := (le_max_right _ _).trans hk
  have hkk : (Kt : Real) <= k := by exact_mod_cast hkt
  have hbudgetRatio := hKt.trans_le hkk
  have hbudget : T * primeWeightLowerConstant + 1 < (1 - T * v) * k := by
    have h := mul_lt_mul_of_pos_right hbudgetRatio (sub_pos.mpr hmargin)
    have hc : ((T * primeWeightLowerConstant + 1) / (1 - T * v)) * (1 - T * v) =
        T * primeWeightLowerConstant + 1 := by
      field_simp [ne_of_gt (sub_pos.mpr hmargin)]
    rw [hc] at h
    nlinarith only [h]
  have hw := hKw.2 k hkw n hn hlow hhigh
  have hk4 : 4 <= k := hKw.1.trans hkw
  have hk0 : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have ha : (0 : Real) < u / 2 := by positivity
  have hpos := mul_pos ha hk0
  have hDGRat := (Rat.cast_pos (K := Real)).mp (hpos.trans_le hw.1)
  have hDORat := (Rat.cast_pos (K := Real)).mp (hpos.trans_le hw.2.1)
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
  have lower : forall S R : Real, 0 < S ->
      S <= v * k + primeWeightLowerConstant ->
      ((k - 1 : Nat) : Real) / S <= R -> T < R := by
    intro S R hS hsum hratio
    have hmul := mul_le_mul_of_nonneg_left hsum hT.le
    have hnum : T * S < ((k - 1 : Nat) : Real) := by
      rw [Nat.cast_sub (by omega : 1 <= k), Nat.cast_one]
      nlinarith only [hmul, hbudget]
    have hcancel : (((k - 1 : Nat) : Real) / S) * S = ((k - 1 : Nat) : Real) := by
      field_simp [ne_of_gt hS]
    have hl : T < ((k - 1 : Nat) : Real) / S := by
      nlinarith only [hnum, hcancel, hS]
    exact hl.trans_le hratio
  have hlG := lower _ _ hw.2.2.2.2.1 hw.2.2.1 hrealG
  have hlO := lower _ _ hw.2.2.2.2.2 hw.2.2.2.1 hrealO
  have huG := genericOdd_ratio_le_of_denominator (n + 1) k _ (by omega) ha hw.1
  have huO := ordinary_ratio_le_of_denominator (n + 1) k _ (by omega) ha hw.2.1
  have hinv : 1 / (u / 2) = (2 : Real) / u := by field_simp
  rw [hinv] at huG huO
  simpa only [Rat.cast_div] using
    And.intro hlG (And.intro huG (And.intro hlO
      (And.intro huO (And.intro hsG hsO))))

end PrimeFactorOscillations
