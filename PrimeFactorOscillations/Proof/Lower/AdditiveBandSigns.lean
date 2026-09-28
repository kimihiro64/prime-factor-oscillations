import PrimeFactorOscillations.Helpers.PrimeGapSigns
import PrimeFactorOscillations.Proof.Lower.AdditiveRatios

/-! # Actual density signs on sharp rank bands -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- Sharp additive-band signs, retaining the complete ratio denominator. -/
theorem both_density_gap_signs_eventually_on_additive_band (H : Nat) (b : Real)
    (hb : 1 / (2 * ((H : Real) + 1)) < b)
    (hmargin : ((H : Real) + 1) * b < 1) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k -> forall i : Nat,
      2 < PrimeFactorUnimodality.primeAt i ->
      b * k - Real.log 2 <=
        Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) ->
      Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) <=
        b * k + Real.log 2 ->
      (PrimeFactorUnimodality.primeAt (i + 1) <= PrimeFactorUnimodality.primeAt i + H ->
        genericOddDensity k i < genericOddDensity k (i + 1) /\
        ordinaryDensity k i < ordinaryDensity k (i + 1)) /\
      (PrimeFactorUnimodality.primeAt i + 4 * (H + 1) <=
          PrimeFactorUnimodality.primeAt (i + 1) ->
        genericOddDensity k (i + 1) < genericOddDensity k i /\
        ordinaryDensity k (i + 1) < ordinaryDensity k i) := by
  have hH : (0 : Real) < (H : Real) + 1 := by positivity
  have hb0 : 0 < b := (by positivity : (0 : Real) < 1 / (2 * ((H : Real) + 1))).trans hb
  have hhighConst : 1 / (((2 : Real) / 3) * b) <= 3 * ((H : Real) + 1) := by
    have hmul := mul_lt_mul_of_pos_left hb (show (0 : Real) < 2 * ((H : Real) + 1) by positivity)
    have hcancel : (2 * ((H : Real) + 1)) * (1 / (2 * ((H : Real) + 1))) = 1 := by field_simp
    rw [hcancel] at hmul
    have hd : (0 : Real) < (2 / 3) * b := by positivity
    have hc : (1 / ((2 / 3) * b)) * ((2 / 3) * b) = (1 : Real) := by field_simp
    by_contra h
    have hgt : 3 * ((H : Real) + 1) < 1 / ((2 / 3) * b) := lt_of_not_ge h
    have hprod := mul_lt_mul_of_pos_right hgt hd
    nlinarith
  choose K hK using both_ratios_eventually_in_additive_band ((H : Real) + 1) b hH hb0 hmargin
  refine Exists.intro K (And.intro hK.1 ?_)
  intro k hk i hp hlow hhigh
  have hk4 : 4 <= k := hK.1.trans hk
  have hn : 2 <= PrimeFactorUnimodality.primeAt i - 1 := by omega
  have hcut : PrimeFactorUnimodality.primeAt i - 1 + 1 =
      PrimeFactorUnimodality.primeAt i := by omega
  have hr := hK.2 k hk (PrimeFactorUnimodality.primeAt i - 1) hn hlow hhigh
  rw [hcut] at hr
  apply both_gap_signs_of_ratios k i H (by omega) hp hr.2.2.2.2.1 hr.2.2.2.2.2
  next =>
    constructor
    next => exact_mod_cast hr.1
    next => exact_mod_cast hr.2.1.trans hhighConst
  next =>
    constructor
    next => exact_mod_cast hr.2.2.1
    next => exact_mod_cast hr.2.2.2.1.trans hhighConst

end PrimeFactorOscillations
