import PrimeFactorOscillations.Proof.Upper.CanonicalDescent
import PrimeFactorOscillations.Proof.Upper.IndexCutoff
import PrimeFactorOscillations.Proof.Upper.UniformRatios

/-! # Strict tails located by prime value -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- A cutoff in prime value, rather than just prime index, locates the strict
tail needed by the probability-mass argument. -/
theorem both_densities_eventually_strict_after_prime_value
    (epsilon : Real) (he : 0 < epsilon) :
    exists K : Nat, 2 <= K /\ forall k : Nat, K <= k ->
      forall i : Nat, upperCutoffValue epsilon k + 1 <=
          (PrimeFactorUnimodality.primeAt i : Real) ->
        ordinaryDensity k (i + 1) < ordinaryDensity k i /\
        genericOddDensity k (i + 1) < genericOddDensity k i := by
  choose K hK using both_ratios_eventually_at_scale epsilon he
  let B : Real := 1 / ((1 : Real) / 3 + epsilon / 4)
  let delta : Real := 3 - B
  have hB : B < 3 := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 1 / 3)
      (by linarith : (1 : Real) / 3 < 1 / 3 + epsilon / 4)
    norm_num at h
    simpa only [B, one_div] using h
  have hd : 0 < delta := by dsimp only [delta]; linarith
  choose Q hQ using exists_nat_gt ((3 : Real) / delta)
  refine Exists.intro (max K Q) (And.intro (hK.1.trans (le_max_left _ _)) ?_)
  intro k hk i hpValue
  have hkOriginal : K <= k := (le_max_left K Q).trans hk
  have hkTwo : 2 <= k := hK.1.trans hkOriginal
  have hQk : (Q : Real) <= k := by exact_mod_cast (le_max_right K Q).trans hk
  have hscaled := mul_lt_mul_of_pos_right (hQ.trans_le hQk) hd
  have hcancel : ((3 : Real) / delta) * delta = 3 := by
    field_simp [ne_of_gt hd]
  rw [hcancel] at hscaled
  have hdBound : (3 : Real) <= delta * k := by nlinarith only [hscaled]
  have hlinear := upperCutoffValue_ge_linear epsilon he.le k
  have hk0 : (0 : Real) <= k := Nat.cast_nonneg k
  have hpR : (2 : Real) < PrimeFactorUnimodality.primeAt i := by linarith
  have hp : 2 < PrimeFactorUnimodality.primeAt i := by exact_mod_cast hpR
  have hn : 2 <= PrimeFactorUnimodality.primeAt i - 1 := by omega
  have hprefix : upperCutoffValue epsilon k <=
      ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) := by
    rw [Nat.cast_sub (show 1 <= PrimeFactorUnimodality.primeAt i by omega), Nat.cast_one]
    linarith only [hpValue]
  have hscale : ((1 : Real) / 3 + epsilon / 2) * k <=
      Real.log (Real.log ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real)) := by
    have hpos : 0 < upperCutoffValue epsilon k := by
      dsimp [upperCutoffValue]
      positivity
    have hlog := Real.log_le_log hpos hprefix
    rw [upperCutoffValue, Real.log_exp] at hlog
    have hloglog := Real.log_le_log (Real.exp_pos _) hlog
    simpa only [Real.log_exp] using hloglog
  have hcontrols := hK.2 k hkOriginal (PrimeFactorUnimodality.primeAt i - 1) hn hscale
  have hrestore : PrimeFactorUnimodality.primeAt i - 1 + 1 =
      PrimeFactorUnimodality.primeAt i := by omega
  rw [hrestore] at hcontrols
  have hD : (0 : Real) < (PrimeFactorUnimodality.primeAt i : Real) - 2 := by linarith
  have hlinearD : (k : Real) / 3 <
      (PrimeFactorUnimodality.primeAt i : Real) - 2 := by linarith
  have hbudget := mul_lt_mul_of_pos_left hlinearD hd
  have hstrict : 1 < delta * ((PrimeFactorUnimodality.primeAt i : Real) - 2) := by
    nlinarith only [hbudget, hdBound]
  have hinverse : 1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) < delta := by
    by_contra h
    have hle : delta <= 1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) :=
      le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hle hD.le
    have hc : (1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2)) *
        ((PrimeFactorUnimodality.primeAt i : Real) - 2) = 1 := by
      field_simp [ne_of_gt hD]
    rw [hc] at hmul
    linarith only [hmul, hstrict]
  have hmargin : B < 3 - 1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) := by
    dsimp only [delta] at hinverse
    linarith
  exact And.intro
    (ordinary_density_lt_of_real_ratio k i hkTwo hp hcontrols.2.2.2.2
      (hcontrols.2.1.trans_lt hcontrols.2.2.1))
    (genericOdd_density_lt_of_real_ratio k i B hkTwo hp hcontrols.2.2.2.1
      hcontrols.1 hmargin)

end PrimeFactorOscillations
