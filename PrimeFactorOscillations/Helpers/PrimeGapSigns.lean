import PrimeFactorOscillations.Helpers.PrimeDensitySteps

/-! # Exact density signs from adjacent prime gaps -/

namespace PrimeFactorOscillations

theorem genericOdd_density_step_gt_iff (k i : Nat) (hk : 2 <= k)
    (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hdegree : k - 1 <= (oddPrimesBelow (PrimeFactorUnimodality.primeAt i)).length) :
    genericOddDensity k i < genericOddDensity k (i + 1) <->
      1 / genericOddEta (PrimeFactorUnimodality.primeAt (i + 1)) -
        1 / genericOddEta (PrimeFactorUnimodality.primeAt i) + 1 <
      finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2) /
        finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) := by
  have hq : 2 < PrimeFactorUnimodality.primeAt (i + 1) :=
    hp.trans (PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i))
  have hindex : k - 2 + 1 = k - 1 := by omega
  have hF : 0 < finiteLocalMass genericOddEta
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2 + 1) := by
    rw [hindex]
    exact genericOdd_prefix_mass_pos _ _ hdegree
  have h := localStep_gt_iff genericOddEta
    (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2)
    (PrimeFactorUnimodality.primeAt i) (PrimeFactorUnimodality.primeAt (i + 1))
    (genericOddEta_pos _ hp) (genericOddEta_pos _ hq) hF
  rw [genericOdd_density_succ]
  simpa only [genericOddDensity, localRankDensity, hindex] using h

theorem genericOdd_threshold_between_gap_and_succ (p q : Nat)
    (hp : 2 < p) (hpq : p <= q) :
    (q : Rat) - p <= 1 / genericOddEta q - 1 / genericOddEta p + 1 /\
    1 / genericOddEta q - 1 / genericOddEta p + 1 <= (q : Rat) - p + 1 := by
  have hq : 2 < q := hp.trans_le hpq
  have hpR : (3 : Rat) <= p := by exact_mod_cast (show 3 <= p by omega)
  have hpqR : (p : Rat) <= q := by exact_mod_cast hpq
  have hpinv := div_le_div_of_nonneg_left (by norm_num : (0 : Rat) <= 1)
    (by norm_num : (0 : Rat) < 1) (show (1 : Rat) <= p - 2 by linarith)
  have hmono := div_le_div_of_nonneg_left (by norm_num : (0 : Rat) <= 1)
    (show (0 : Rat) < p - 2 by linarith) (show (p : Rat) - 2 <= q - 2 by linarith)
  have hqinv : (0 : Rat) <= 1 / ((q : Rat) - 2) :=
    div_nonneg (by norm_num) (by linarith)
  rw [genericOddEta_reciprocal q hq, genericOddEta_reciprocal p hp]
  exact And.intro (by linarith) (by linarith)

/-- Exact density signs from the full ratio band and the actual adjacent gap. -/
theorem both_gap_signs_of_ratios (k i H : Nat) (hk : 2 <= k)
    (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hsG : k - 1 <= (oddPrimesBelow (PrimeFactorUnimodality.primeAt i)).length)
    (hsO : k - 1 <=
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)).length)
    (hG : (H : Rat) + 1 <
        finiteLocalMass genericOddEta
            (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2) /
          finiteLocalMass genericOddEta
            (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) /\
      finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2) /
        finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) <=
            3 * ((H : Rat) + 1))
    (hO : (H : Rat) + 1 < PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) /\
      PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) <=
          3 * ((H : Rat) + 1)) :
    (PrimeFactorUnimodality.primeAt (i + 1) <= PrimeFactorUnimodality.primeAt i + H ->
      genericOddDensity k i < genericOddDensity k (i + 1) /\
      ordinaryDensity k i < ordinaryDensity k (i + 1)) /\
    (PrimeFactorUnimodality.primeAt i + 4 * (H + 1) <=
        PrimeFactorUnimodality.primeAt (i + 1) ->
      genericOddDensity k (i + 1) < genericOddDensity k i /\
      ordinaryDensity k (i + 1) < ordinaryDensity k i) := by
  have hpq := (PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i)).le
  have htG := genericOdd_threshold_between_gap_and_succ
    (PrimeFactorUnimodality.primeAt i) (PrimeFactorUnimodality.primeAt (i + 1)) hp hpq
  have hindex : k - 2 + 1 = k - 1 := by omega
  have hrank : k - 2 + 2 = k := by omega
  have hri : k - 2 + 1 <= i := by
    rw [PrimeFactorUnimodality.primesBelow_primeAt_length] at hsO
    omega
  have hH0 : (0 : Rat) <= H := Nat.cast_nonneg H
  constructor
  next =>
    intro hshort
    have hshortR : (PrimeFactorUnimodality.primeAt (i + 1) : Rat) <=
        (PrimeFactorUnimodality.primeAt i : Rat) + H := by exact_mod_cast hshort
    have hgs : genericOddDensity k i < genericOddDensity k (i + 1) := by
      apply (genericOdd_density_step_gt_iff k i hk hp hsG).mpr
      linarith only [htG.2, hshortR, hG.1]
    have hgap : ((PrimeFactorUnimodality.primeGap i + 1 : Nat) : Rat) <= (H : Rat) + 1 := by
      exact_mod_cast (show PrimeFactorUnimodality.primeGap i + 1 <= H + 1 by
        unfold PrimeFactorUnimodality.primeGap
        omega)
    have hos := (PrimeFactorUnimodality.primeDensityStep_iff_ratio_gap (k - 2) i hri).mpr
      (by simpa only [hindex] using hgap.trans_lt hO.1)
    exact And.intro hgs (by simpa only [ordinaryDensity, hrank] using hos)
  next =>
    intro hlong
    have hlongR : (PrimeFactorUnimodality.primeAt i : Rat) + 4 * ((H : Rat) + 1) <=
        (PrimeFactorUnimodality.primeAt (i + 1) : Rat) := by exact_mod_cast hlong
    have hgs : genericOddDensity k (i + 1) < genericOddDensity k i := by
      apply (genericOdd_density_step_lt_iff k i hk hp hsG).mpr
      linarith only [htG.1, hlongR, hG.2, hH0]
    have hgap : (4 : Rat) * ((H : Rat) + 1) <=
        ((PrimeFactorUnimodality.primeGap i + 1 : Nat) : Rat) := by
      exact_mod_cast (show 4 * (H + 1) <= PrimeFactorUnimodality.primeGap i + 1 by
        unfold PrimeFactorUnimodality.primeGap
        omega)
    have hos := (PrimeFactorUnimodality.primeDensityStep_lt_iff_ratio_lt_gap (k - 2) i hri).mpr
      (by rw [hindex]; linarith only [hO.2, hgap, hH0])
    exact And.intro hgs (by simpa only [ordinaryDensity, hrank] using hos)

end PrimeFactorOscillations
