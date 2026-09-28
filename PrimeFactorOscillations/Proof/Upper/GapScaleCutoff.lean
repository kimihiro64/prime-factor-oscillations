import PrimeFactorOscillations.Helpers.PrimeDensitySteps
import PrimeFactorOscillations.Proof.Upper.GeneralScaleRatios

set_option autoImplicit false

/-! # Sharp descent scales from a lower bound on the actual prime gap -/

namespace PrimeFactorOscillations

/-- The exact local thresholds retain an arbitrary lower bound on the gap,
including the decaying correction in the generic odd family. -/
theorem both_densities_descend_of_gap_ratio (H k i : Nat) (B : Real)
    (hk : 2 <= k) (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hgap : PrimeFactorUnimodality.primeAt i + H <=
      PrimeFactorUnimodality.primeAt (i + 1))
    (hdegreeG : k - 1 <= (oddPrimesBelow (PrimeFactorUnimodality.primeAt i)).length)
    (hdegreeO : k - 1 <=
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)).length)
    (hRatioG :
      ((finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2) /
        finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) :
          Rat) : Real) <= B)
    (hRatioO : (PrimeFactorUnimodality.densityRatio
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) :
        Real) <= B)
    (hMargin : B < (H : Real) + 1 -
      1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2)) :
    genericOddDensity k (i + 1) < genericOddDensity k i /\
      ordinaryDensity k (i + 1) < ordinaryDensity k i := by
  have hpq : PrimeFactorUnimodality.primeAt i <
      PrimeFactorUnimodality.primeAt (i + 1) :=
    PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i)
  have hq : 2 < PrimeFactorUnimodality.primeAt (i + 1) := hp.trans hpq
  have hlowRat : (H : Rat) + 1 -
      1 / ((PrimeFactorUnimodality.primeAt i : Rat) - 2) <=
      1 / genericOddEta (PrimeFactorUnimodality.primeAt (i + 1)) -
        1 / genericOddEta (PrimeFactorUnimodality.primeAt i) + 1 := by
    rw [genericOddEta_reciprocal _ hq, genericOddEta_reciprocal _ hp]
    have hgapR : (PrimeFactorUnimodality.primeAt i : Rat) + H <=
        PrimeFactorUnimodality.primeAt (i + 1) := by exact_mod_cast hgap
    have hqR : (2 : Rat) < PrimeFactorUnimodality.primeAt (i + 1) := by exact_mod_cast hq
    have hnonneg : (0 : Rat) <=
        1 / ((PrimeFactorUnimodality.primeAt (i + 1) : Rat) - 2) :=
      div_nonneg (by norm_num) (by linarith)
    linarith
  have hlow : (H : Real) + 1 -
      1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) <=
      ((1 / genericOddEta (PrimeFactorUnimodality.primeAt (i + 1)) -
        1 / genericOddEta (PrimeFactorUnimodality.primeAt i) + 1 : Rat) : Real) := by
    simpa only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le (K := Real)).mpr hlowRat
  refine And.intro ?_ ?_
  next =>
    exact (genericOdd_density_step_lt_iff k i hk hp hdegreeG).mpr
      ((Rat.cast_lt (K := Real)).mp (hRatioG.trans_lt (hMargin.trans_le hlow)))
  next =>
    have hpR : (2 : Real) < PrimeFactorUnimodality.primeAt i := by exact_mod_cast hp
    have hnonneg : (0 : Real) <= 1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) :=
      div_nonneg (by norm_num) (by linarith)
    have hsmallR : (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) :
          Real) < (H : Real) + 1 := by linarith only [hRatioO, hMargin, hnonneg]
    have hsmall : PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) <
          (H : Rat) + 1 := by exact_mod_cast hsmallR
    have hgapN : H <= PrimeFactorUnimodality.primeGap i := by
      unfold PrimeFactorUnimodality.primeGap
      omega
    have hgapRat : (H : Rat) + 1 <= ((PrimeFactorUnimodality.primeGap i + 1 : Nat) : Rat) := by
      exact_mod_cast Nat.add_le_add_right hgapN 1
    have hri : k - 2 + 1 <= i := by
      rw [PrimeFactorUnimodality.primesBelow_primeAt_length] at hdegreeO
      omega
    have hindex : k - 2 + 1 = k - 1 := by omega
    have hrank : k - 2 + 2 = k := by omega
    have hstep := (PrimeFactorUnimodality.primeDensityStep_lt_iff_ratio_lt_gap
      (k - 2) i hri).mpr (by simpa only [hindex] using hsmall.trans_le hgapRat)
    simpa only [ordinaryDensity, hrank] using hstep

/-- For every b>1/(H+1), all sufficiently large ranks descend at every
sufficiently large prime on that scale whose actual following gap is at least H.
No hypothesis that such a lower gap bound holds globally is smuggled in. -/
theorem both_densities_eventually_descend_above_gap_scale (H : Nat) (b : Real)
    (hb : 1 / ((H : Real) + 1) < b) :
    exists K Q : Nat, 2 <= K /\ 3 <= Q /\ forall k : Nat, K <= k ->
      forall i : Nat, Q <= PrimeFactorUnimodality.primeAt i ->
      PrimeFactorUnimodality.primeAt i + H <= PrimeFactorUnimodality.primeAt (i + 1) ->
      b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) ->
      genericOddDensity k (i + 1) < genericOddDensity k i /\
        ordinaryDensity k (i + 1) < ordinaryDensity k i := by
  let a : Real := (1 / ((H : Real) + 1) + b) / 2
  have hH : (0 : Real) < (H : Real) + 1 := by positivity
  have hbase : (0 : Real) < 1 / ((H : Real) + 1) := by positivity
  have hba : 1 / ((H : Real) + 1) < a := by dsimp [a]; linarith
  have ha : 0 < a := hbase.trans hba
  have hab : a < b := by dsimp [a]; linarith
  have hinv : 1 / a < (H : Real) + 1 := by
    have h := one_div_lt_one_div_of_lt hbase hba
    have hc : (1 : Real) / (1 / ((H : Real) + 1)) = (H : Real) + 1 := by field_simp
    rwa [hc] at h
  let delta : Real := (H : Real) + 1 - 1 / a
  have hd : 0 < delta := by dsimp [delta]; linarith only [hinv]
  choose K hK using both_ratios_eventually_below_of_scale a b ha hab
  choose Q hQ using exists_nat_gt (max (3 : Real) (2 + 1 / delta))
  have hQthree : (3 : Real) < Q := (le_max_left _ _).trans_lt hQ
  have hQnat : 3 <= Q := by exact_mod_cast hQthree.le
  refine Exists.intro K (Exists.intro Q (And.intro hK.1 (And.intro hQnat ?_)))
  intro k hk i hp hgap hscale
  have hpThree : 3 <= PrimeFactorUnimodality.primeAt i := hQnat.trans hp
  have hpgt : 2 < PrimeFactorUnimodality.primeAt i := by omega
  have hpR : (Q : Real) <= PrimeFactorUnimodality.primeAt i := by exact_mod_cast hp
  have hlarge : 1 / delta < (PrimeFactorUnimodality.primeAt i : Real) - 2 := by
    have h := (le_max_right _ _).trans_lt hQ
    linarith only [h, hpR]
  have hcorrection : 1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) < delta := by
    have h := one_div_lt_one_div_of_lt (div_pos (by norm_num) hd) hlarge
    have hc : (1 : Real) / (1 / delta) = delta := by field_simp
    rwa [hc] at h
  have hmargin : 1 / a < (H : Real) + 1 -
      1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) := by
    dsimp only [delta] at hcorrection
    linarith only [hcorrection]
  have hr := hK.2 k hk (PrimeFactorUnimodality.primeAt i - 1) (by omega) hscale
  rw [Nat.sub_add_cancel (show 1 <= PrimeFactorUnimodality.primeAt i by omega)] at hr
  exact both_densities_descend_of_gap_ratio H k i (1 / a) (hK.1.trans hk) hpgt
    hgap hr.2.2.1 hr.2.2.2 hr.1 hr.2.1 hmargin

/-- Any sufficiently late ascent beyond a scale strictly greater than 1/5
must occur across a twin-prime gap, for either canonical density. -/
theorem ascent_above_one_fifth_forces_twins (b : Real) (hb : (1 : Real) / 5 < b) :
    exists K Q : Nat, 2 <= K /\ 3 <= Q /\ forall k : Nat, K <= k ->
      forall i : Nat, Q <= PrimeFactorUnimodality.primeAt i ->
      b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) ->
      (ordinaryDensity k i < ordinaryDensity k (i + 1) \/
        genericOddDensity k i < genericOddDensity k (i + 1)) ->
      PrimeFactorUnimodality.primeAt (i + 1) = PrimeFactorUnimodality.primeAt i + 2 := by
  choose K Q h using both_densities_eventually_descend_above_gap_scale 4 b
    (by convert hb using 1 <;> norm_num)
  refine Exists.intro K (Exists.intro Q (And.intro h.1 (And.intro h.2.1 ?_)))
  intro k hk i hp hscale hascent
  have hpgt : 2 < PrimeFactorUnimodality.primeAt i := by
    have hthree := h.2.1.trans hp
    omega
  have hpq : PrimeFactorUnimodality.primeAt i <
      PrimeFactorUnimodality.primeAt (i + 1) :=
    PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i)
  have hqgt := hpgt.trans hpq
  have hpOdd := (PrimeFactorUnimodality.prime_primeAt i).eq_two_or_odd.resolve_left
    (ne_of_gt hpgt)
  have hqOdd := (PrimeFactorUnimodality.prime_primeAt (i + 1)).eq_two_or_odd.resolve_left
    (ne_of_gt hqgt)
  by_contra hnot
  have hgap : PrimeFactorUnimodality.primeAt i + 4 <=
      PrimeFactorUnimodality.primeAt (i + 1) := by omega
  have hdescent := h.2.2 k hk i hp hgap hscale
  rcases hascent with hordinary | hgeneric
  next => exact (not_lt_of_ge hdescent.2.le) hordinary
  next => exact (not_lt_of_ge hdescent.1.le) hgeneric

/-- An independently established supply of such late ascents would prove
twin-prime infinitude. Both the scale and ascent-supply premise are explicit. -/
theorem infinitely_many_twins_of_late_ascent_supply (b : Real)
    (hb : (1 : Real) / 5 < b)
    (hsupply : forall K Q : Nat, exists k i : Nat, K <= k /\
      Q <= PrimeFactorUnimodality.primeAt i /\
      b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) /\
      (ordinaryDensity k i < ordinaryDensity k (i + 1) \/
        genericOddDensity k i < genericOddDensity k (i + 1))) :
    forall X : Nat, exists p : Nat, X <= p /\ Nat.Prime p /\ Nat.Prime (p + 2) := by
  choose K Q h using ascent_above_one_fifth_forces_twins b hb
  intro X
  choose k i hki using hsupply K (max Q X)
  have hpQ := (le_max_left Q X).trans hki.2.1
  have hpX := (le_max_right Q X).trans hki.2.1
  have hpair := h.2.2 k hki.1 i hpQ hki.2.2.1 hki.2.2.2
  refine Exists.intro (PrimeFactorUnimodality.primeAt i)
    (And.intro hpX (And.intro (PrimeFactorUnimodality.prime_primeAt i) ?_))
  rw [<- hpair]
  exact PrimeFactorUnimodality.prime_primeAt (i + 1)

end PrimeFactorOscillations
