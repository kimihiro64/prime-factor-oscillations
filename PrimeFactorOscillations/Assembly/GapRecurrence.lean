import PrimeFactorOscillations.Proof.Lower.RecurrentGaps
import PrimeFactorOscillations.Proof.Upper.GapScaleCutoff

/-! # Exact recurring-gap and late-ascent equivalence -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/- The converse has no imported bounded-gap premise. -/
theorem recurrent_gaps_below_of_late_ascents (H : Nat) (b : Real)
    (hb : 1 / ((H : Real) + 1) < b)
    (hsupply : forall K Q : Nat, exists k i : Nat, K <= k /\
      Q <= PrimeFactorUnimodality.primeAt i /\
      b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) /\
      (ordinaryDensity k i < ordinaryDensity k (i + 1) \/
        genericOddDensity k i < genericOddDensity k (i + 1))) :
    forall Q : Nat, exists i : Nat, Q <= PrimeFactorUnimodality.primeAt i /\
      PrimeFactorUnimodality.primeAt (i + 1) < PrimeFactorUnimodality.primeAt i + H := by
  choose K Q0 h using both_densities_eventually_descend_above_gap_scale H b hb
  intro Q
  choose k i hi using hsupply K (max Q Q0)
  have hpQ : Q <= PrimeFactorUnimodality.primeAt i := (le_max_left Q Q0).trans hi.2.1
  have hpQ0 : Q0 <= PrimeFactorUnimodality.primeAt i := (le_max_right Q Q0).trans hi.2.1
  refine Exists.intro i (And.intro hpQ ?_)
  by_contra hnot
  have hgap : PrimeFactorUnimodality.primeAt i + H <=
      PrimeFactorUnimodality.primeAt (i + 1) := le_of_not_gt hnot
  have hdesc := h.2.2 k hi.1 i hpQ0 hgap hi.2.2.1
  rcases hi.2.2.2 with ho | hg
  next => exact (not_lt_of_ge hdesc.2.le) ho
  next => exact (not_lt_of_ge hdesc.1.le) hg

/-- On each interval between adjacent reciprocal thresholds, recurring gaps
at most H are equivalent to simultaneous late ascents in both canonical laws. -/
theorem recurrent_short_gaps_iff_late_ascents (H : Nat) (hH : 1 <= H) (b : Real)
    (hb : 1 / ((H : Real) + 2) < b)
    (hupper : b < 1 / ((H : Real) + 1)) :
    (forall Q : Nat, exists i : Nat, Q <= PrimeFactorUnimodality.primeAt i /\
      PrimeFactorUnimodality.primeAt (i + 1) <= PrimeFactorUnimodality.primeAt i + H) <->
    (forall K Q : Nat, exists k i : Nat, K <= k /\
      Q <= PrimeFactorUnimodality.primeAt i /\
      b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) /\
      genericOddDensity k i < genericOddDensity k (i + 1) /\
      ordinaryDensity k i < ordinaryDensity k (i + 1)) := by
  have hHreal : (1 : Real) <= H := by exact_mod_cast hH
  have hpos : (0 : Real) < (H : Real) + 1 := by positivity
  have hhalf : 1 / (2 * ((H : Real) + 1)) < b := by
    have h := one_div_lt_one_div_of_lt
      (by positivity : (0 : Real) < (H : Real) + 2)
      (by linarith : (H : Real) + 2 < 2 * ((H : Real) + 1))
    exact h.trans hb
  have hmargin : ((H : Real) + 1) * b < 1 := by
    have h := mul_lt_mul_of_pos_left hupper hpos
    have hc : ((H : Real) + 1) * (1 / ((H : Real) + 1)) = 1 := by field_simp
    rwa [hc] at h
  constructor
  next => exact late_ascents_of_recurrent_short_gaps H hH b hhalf hmargin
  next =>
    intro hs Q
    have hs' : forall K Q : Nat, exists k i : Nat, K <= k /\
        Q <= PrimeFactorUnimodality.primeAt i /\
        b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) /\
        (ordinaryDensity k i < ordinaryDensity k (i + 1) \/
          genericOddDensity k i < genericOddDensity k (i + 1)) := by
      intro K Q
      choose k i hi using hs K Q
      exact Exists.intro k (Exists.intro i (And.intro hi.1
        (And.intro hi.2.1 (And.intro hi.2.2.1 (Or.inl hi.2.2.2.2)))))
    have hb' : 1 / (((H + 1 : Nat) : Real) + 1) < b := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hb
    choose i hi using recurrent_gaps_below_of_late_ascents (H + 1) b hb' hs' Q
    exact Exists.intro i (And.intro hi.1 (by omega))

/-- If h is the least recurring gap (expressed by recurrence and an eventual
lower gap bound), 1/(h+1) is the exact critical late-ascent scale. This is the
threshold formulation; no maximum or limsup notation is being assumed. -/
theorem late_ascent_critical_scale (h : Nat) (hh : 1 <= h)
    (hrec : forall Q : Nat, exists i : Nat,
      Q <= PrimeFactorUnimodality.primeAt i /\
      PrimeFactorUnimodality.primeAt (i + 1) <=
        PrimeFactorUnimodality.primeAt i + h)
    (hmin : exists Q : Nat, forall i : Nat, Q <= PrimeFactorUnimodality.primeAt i ->
      PrimeFactorUnimodality.primeAt i + h <= PrimeFactorUnimodality.primeAt (i + 1)) :
    (forall b : Real, 0 < b -> b < 1 / ((h : Real) + 1) ->
      forall K Q : Nat, exists k i : Nat, K <= k /\
        Q <= PrimeFactorUnimodality.primeAt i /\
        b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) /\
        genericOddDensity k i < genericOddDensity k (i + 1) /\
        ordinaryDensity k i < ordinaryDensity k (i + 1)) /\
    (forall b : Real, 1 / ((h : Real) + 1) < b ->
      exists K Q : Nat, forall k i : Nat, K <= k ->
        Q <= PrimeFactorUnimodality.primeAt i ->
        b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) ->
        genericOddDensity k (i + 1) < genericOddDensity k i /\
        ordinaryDensity k (i + 1) < ordinaryDensity k i) := by
  constructor
  next =>
    intro b hb hupper
    exact late_ascents_below_recurrent_gap_scale h hh b hb hupper hrec
  next =>
    intro b hb
    choose Q0 hQ0 using hmin
    choose K Q1 ht using both_densities_eventually_descend_above_gap_scale h b hb
    refine Exists.intro K (Exists.intro (max Q0 Q1) ?_)
    intro k i hk hi hscale
    have hp0 := (le_max_left Q0 Q1).trans hi
    have hp1 := (le_max_right Q0 Q1).trans hi
    exact ht.2.2 k hk i hp1 (hQ0 i hp0) hscale

end PrimeFactorOscillations
