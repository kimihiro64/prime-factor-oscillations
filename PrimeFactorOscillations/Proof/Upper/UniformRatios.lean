import PrimeFactorOscillations.Proof.Upper.RatioBounds
import PrimeFactorOscillations.Proof.Upper.UniformDenominator

set_option autoImplicit false

/-! # Unconditional uniform ratio cutoff below the odd-prime gap threshold -/

namespace PrimeFactorOscillations

/-- For all sufficiently large ranks, both ratios are uniformly below three
at every cutoff on the specified logarithmic scale. -/
theorem both_ratios_eventually_at_scale (epsilon : Real) (he : 0 < epsilon) :
    exists K : Nat, 2 <= K /\ forall k : Nat, K <= k ->
      forall n : Nat, 2 <= n ->
      ((1 : Real) / 3 + epsilon / 2) * k <= Real.log (Real.log n) ->
      (((finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 2) /
          finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) :
            Rat) : Real) <= 1 / ((1 : Real) / 3 + epsilon / 4)) /\
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (n + 1)) (k - 1) : Real) <=
          1 / ((1 : Real) / 3 + epsilon / 4) /\
      1 / ((1 : Real) / 3 + epsilon / 4) < 3 /\
      k - 1 <= (oddPrimesBelow (n + 1)).length /\
      k - 1 <= (PrimeFactorUnimodality.primesBelow (n + 1)).length := by
  choose K hK using both_denominators_eventually_at_scale epsilon he
  refine Exists.intro (max 2 K) (And.intro (le_max_left _ _) ?_)
  intro k hk n hn hscale
  have hkTwo : 2 <= k := (le_max_left 2 K).trans hk
  have hden := hK.2 k ((le_max_right 2 K).trans hk) n hn hscale
  have ha : (0 : Real) < 1 / 3 + epsilon / 4 := by linarith
  have hbound : 1 / ((1 : Real) / 3 + epsilon / 4) < 3 := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 1 / 3)
      (by linarith : (1 : Real) / 3 < 1 / 3 + epsilon / 4)
    norm_num at h
    simpa only [one_div] using h
  exact And.intro
    (genericOdd_ratio_le_of_denominator (n + 1) k _ hkTwo ha hden.1.1)
    (And.intro (ordinary_ratio_le_of_denominator (n + 1) k _ hkTwo ha hden.2.1)
      (And.intro hbound (And.intro
        (genericOdd_degree_supported_of_complement_pos (n + 1) k
          ((Rat.cast_pos (K := Real)).mp hden.1.2))
        (ordinary_degree_supported_of_complement_pos (n + 1) k
          ((Rat.cast_pos (K := Real)).mp hden.2.2)))))

end PrimeFactorOscillations
