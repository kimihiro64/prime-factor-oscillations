import PrimeFactorOscillations.Helpers.PrimeDensitySteps

set_option autoImplicit false

/-! # Strict descent of the actual indexed density sequences -/

namespace PrimeFactorOscillations

/-- The generic density decreases once its uniform ratio bound fits below the
true reciprocal threshold, including the decaying finite-prime correction. -/
theorem genericOdd_density_lt_of_real_ratio (k i : Nat) (B : Real)
    (hk : 2 <= k) (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hdegree : k - 1 <= (oddPrimesBelow (PrimeFactorUnimodality.primeAt i)).length)
    (hRatio :
      ((finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2) /
        finiteLocalMass genericOddEta
          (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) : Rat) :
          Real) <= B)
    (hMargin : B < 3 - 1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2)) :
    genericOddDensity k (i + 1) < genericOddDensity k i := by
  have hlowRat := genericOdd_threshold_lower (PrimeFactorUnimodality.primeAt i)
    (PrimeFactorUnimodality.primeAt (i + 1)) hp (primeAt_gap_ge_two i hp)
  have hlow : (3 : Real) - 1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) <=
      ((1 / genericOddEta (PrimeFactorUnimodality.primeAt (i + 1)) -
        1 / genericOddEta (PrimeFactorUnimodality.primeAt i) + 1 : Rat) : Real) := by
    simpa only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le (K := Real)).mpr hlowRat
  have hreal := hRatio.trans_lt (hMargin.trans_le hlow)
  exact (genericOdd_density_step_lt_iff k i hk hp hdegree).mpr
    ((Rat.cast_lt (K := Real)).mp hreal)

/-- The ordinary density decreases once its actual ratio is below three. -/
theorem ordinary_density_lt_of_real_ratio (k i : Nat)
    (hk : 2 <= k) (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hdegree : k - 1 <=
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)).length)
    (hRatio : (PrimeFactorUnimodality.densityRatio
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) : Real) < 3) :
    ordinaryDensity k (i + 1) < ordinaryDensity k i := by
  have hindex : k - 2 + 1 = k - 1 := by omega
  have hrank : k - 2 + 2 = k := by omega
  have hri : k - 2 + 1 <= i := by
    rw [PrimeFactorUnimodality.primesBelow_primeAt_length] at hdegree
    omega
  have hthree : PrimeFactorUnimodality.densityRatio
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) <
        (3 : Rat) := by
    apply (Rat.cast_lt (K := Real)).mp
    simpa only [Rat.cast_ofNat] using hRatio
  have hgap : (3 : Rat) <= ((PrimeFactorUnimodality.primeGap i + 1 : Nat) : Rat) := by
    exact_mod_cast (show 3 <= PrimeFactorUnimodality.primeGap i + 1 by
      have h := primeGap_ge_two i hp
      omega)
  have hsmall : PrimeFactorUnimodality.densityRatio
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 2 + 1) <
        ((PrimeFactorUnimodality.primeGap i + 1 : Nat) : Rat) := by
    simpa only [hindex] using hthree.trans_le hgap
  have hstep := (PrimeFactorUnimodality.primeDensityStep_lt_iff_ratio_lt_gap
    (k - 2) i hri).mpr hsmall
  simpa only [ordinaryDensity, hrank] using hstep

end PrimeFactorOscillations
