import PrimeFactorOscillations.Helpers.PrimeGapSigns
import PrimeFactorOscillations.Proof.Lower.ScaleRatios

/-! # Uniform descent and ascent signs on the lower rank band -/

namespace PrimeFactorOscillations

/-- The actual gap-sign margins hold uniformly on the chosen lower rank band. -/
theorem both_density_gap_signs_eventually_on_band (H : Nat) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k -> forall i : Nat,
      2 < PrimeFactorUnimodality.primeAt i ->
      ((3 : Real) / 4) * (1 / (2 * ((H : Real) + 1))) * k <=
        Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) ->
      Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) <=
        ((5 : Real) / 4) * (1 / (2 * ((H : Real) + 1))) * k ->
      (PrimeFactorUnimodality.primeAt (i + 1) <= PrimeFactorUnimodality.primeAt i + H ->
        genericOddDensity k i < genericOddDensity k (i + 1) /\
        ordinaryDensity k i < ordinaryDensity k (i + 1)) /\
      (PrimeFactorUnimodality.primeAt i + 4 * (H + 1) <=
          PrimeFactorUnimodality.primeAt (i + 1) ->
        genericOddDensity k (i + 1) < genericOddDensity k i /\
        ordinaryDensity k (i + 1) < ordinaryDensity k i) := by
  let beta : Real := 1 / (2 * ((H : Real) + 1))
  have hb : 0 < beta := by dsimp [beta]; positivity
  have hH : Not ((H : Real) + 1 = 0) := ne_of_gt (by positivity)
  have hlowConst : 1 / (2 * beta) = (H : Real) + 1 := by
    dsimp [beta]
    field_simp
  have hhighConst : 1 / (((2 : Real) / 3) * beta) = 3 * ((H : Real) + 1) := by
    dsimp [beta]
    field_simp
  choose K hK using both_ratios_eventually_in_lower_band beta hb
  refine Exists.intro K (And.intro hK.1 ?_)
  intro k hk i hp hlow hhigh
  have hk4 : 4 <= k := hK.1.trans hk
  have hn : 2 <= PrimeFactorUnimodality.primeAt i - 1 := by omega
  have hcut : PrimeFactorUnimodality.primeAt i - 1 + 1 =
      PrimeFactorUnimodality.primeAt i := by omega
  have hr := hK.2 k hk (PrimeFactorUnimodality.primeAt i - 1) hn hlow hhigh
  rw [hcut, hlowConst, hhighConst] at hr
  apply both_gap_signs_of_ratios k i H (by omega) hp hr.2.2.2.2.1 hr.2.2.2.2.2
  next =>
    constructor
    next => exact_mod_cast hr.1
    next => exact_mod_cast hr.2.1
  next =>
    constructor
    next => exact_mod_cast hr.2.2.1
    next => exact_mod_cast hr.2.2.2.1

end PrimeFactorOscillations
