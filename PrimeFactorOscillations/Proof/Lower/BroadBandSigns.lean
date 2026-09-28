import PrimeFactorOscillations.Helpers.PrimeGapSigns
import PrimeFactorOscillations.Proof.Lower.BroadBandRatios

/-! # Independent short-gap and long-gap thresholds on broad rank bands -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- Uniform signs across an arbitrary fixed broad band. The long-gap barrier
can be chosen independently of the short-gap bound. -/
theorem both_density_gap_signs_eventually_on_broad_band
    (H L : Nat) (u v : Real) (hu : 0 < u)
    (hmargin : ((H : Real) + 1) * v < 1) (hL : 2 / u < (L : Real)) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k -> forall i : Nat,
      2 < PrimeFactorUnimodality.primeAt i ->
      u * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) ->
      Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) <= v * k ->
      (PrimeFactorUnimodality.primeAt (i + 1) <= PrimeFactorUnimodality.primeAt i + H ->
        genericOddDensity k i < genericOddDensity k (i + 1) /\
        ordinaryDensity k i < ordinaryDensity k (i + 1)) /\
      (PrimeFactorUnimodality.primeAt i + L <= PrimeFactorUnimodality.primeAt (i + 1) ->
        genericOddDensity k (i + 1) < genericOddDensity k i /\
        ordinaryDensity k (i + 1) < ordinaryDensity k i) := by
  choose K hK using both_ratios_eventually_in_broad_band
    ((H : Real) + 1) u v (by positivity) hu hmargin
  refine Exists.intro K (And.intro hK.1 ?_)
  intro k hk i hp hlow hhigh
  have hk4 : 4 <= k := hK.1.trans hk
  have hn : 2 <= PrimeFactorUnimodality.primeAt i - 1 := by omega
  have hcut : PrimeFactorUnimodality.primeAt i - 1 + 1 =
      PrimeFactorUnimodality.primeAt i := by omega
  have hr := hK.2 k hk (PrimeFactorUnimodality.primeAt i - 1) hn hlow hhigh
  rw [hcut] at hr
  have hsG := hr.2.2.2.2.1
  have hsO := hr.2.2.2.2.2
  have hGL : (H : Rat) + 1 <
      finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2) /
        finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) := by
    exact_mod_cast hr.1
  have hGU :
      finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2) /
        finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) <
        (L : Rat) := by
    exact_mod_cast hr.2.1.trans_lt hL
  have hOL : (H : Rat) + 1 < PrimeFactorUnimodality.densityRatio
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) := by
    exact_mod_cast hr.2.2.1
  have hOU : PrimeFactorUnimodality.densityRatio
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) <
      (L : Rat) := by
    exact_mod_cast hr.2.2.2.1.trans_lt hL
  have hpq := (PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i)).le
  have htG := genericOdd_threshold_between_gap_and_succ
    (PrimeFactorUnimodality.primeAt i) (PrimeFactorUnimodality.primeAt (i + 1)) hp hpq
  have hindex : k - 2 + 1 = k - 1 := by omega
  have hrank : k - 2 + 2 = k := by omega
  have hri : k - 2 + 1 <= i := by
    rw [PrimeFactorUnimodality.primesBelow_primeAt_length] at hsO
    omega
  constructor
  next =>
    intro hshort
    have hshortR : (PrimeFactorUnimodality.primeAt (i + 1) : Rat) <=
        (PrimeFactorUnimodality.primeAt i : Rat) + H := by exact_mod_cast hshort
    have hgs : genericOddDensity k i < genericOddDensity k (i + 1) := by
      apply (genericOdd_density_step_gt_iff k i (by omega) hp hsG).mpr
      linarith only [htG.2, hshortR, hGL]
    have hgap : ((PrimeFactorUnimodality.primeGap i + 1 : Nat) : Rat) <= (H : Rat) + 1 := by
      exact_mod_cast (show PrimeFactorUnimodality.primeGap i + 1 <= H + 1 by
        unfold PrimeFactorUnimodality.primeGap
        omega)
    have hos := (PrimeFactorUnimodality.primeDensityStep_iff_ratio_gap (k - 2) i hri).mpr
      (by simpa only [hindex] using hgap.trans_lt hOL)
    exact And.intro hgs (by simpa only [ordinaryDensity, hrank] using hos)
  next =>
    intro hlong
    have hlongR : (PrimeFactorUnimodality.primeAt i : Rat) + L <=
        (PrimeFactorUnimodality.primeAt (i + 1) : Rat) := by exact_mod_cast hlong
    have hgs : genericOddDensity k (i + 1) < genericOddDensity k i := by
      apply (genericOdd_density_step_lt_iff k i (by omega) hp hsG).mpr
      linarith only [htG.1, hlongR, hGU]
    have hgap : (L : Rat) <= ((PrimeFactorUnimodality.primeGap i + 1 : Nat) : Rat) := by
      exact_mod_cast (show L <= PrimeFactorUnimodality.primeGap i + 1 by
        unfold PrimeFactorUnimodality.primeGap
        omega)
    have hos := (PrimeFactorUnimodality.primeDensityStep_lt_iff_ratio_lt_gap (k - 2) i hri).mpr
      (by rw [hindex]; exact hOU.trans_le hgap)
    exact And.intro hgs (by simpa only [ordinaryDensity, hrank] using hos)

end PrimeFactorOscillations
