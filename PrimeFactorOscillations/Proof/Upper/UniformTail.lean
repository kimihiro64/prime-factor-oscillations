import PrimeFactorOscillations.Proof.Upper.CanonicalDescent
import PrimeFactorOscillations.Proof.Upper.IndexCutoff
import PrimeFactorOscillations.Proof.Upper.UniformRatios

set_option autoImplicit false

/-! # Uniform strict tails for both canonical density families -/

namespace PrimeFactorOscillations

/-- All scale, support, parity, correction, and ceiling conditions are discharged
before the rank and the later prime index vary. -/
theorem both_densities_eventually_strict_tail (epsilon : Real) (he : 0 < epsilon) :
    exists K : Nat, 2 <= K /\ forall k : Nat, K <= k ->
      (upperCutoffIndex epsilon k : Real) <=
        Real.exp (Real.exp (((1 : Real) / 3 + epsilon) * k)) /\
      forall i : Nat, upperCutoffIndex epsilon k <= i ->
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
  have hep : (0 : Real) < 2 / epsilon := div_pos (by norm_num) he
  have hdp : (0 : Real) < 3 / delta := div_pos (by norm_num) hd
  choose Q hQ using exists_nat_gt ((2 : Real) / epsilon + 3 / delta)
  refine Exists.intro (max K Q) (And.intro (hK.1.trans (le_max_left _ _)) ?_)
  intro k hk
  have hkOriginal : K <= k := (le_max_left K Q).trans hk
  have hkTwo : 2 <= k := hK.1.trans hkOriginal
  have hQk : (Q : Real) <= k := by exact_mod_cast (le_max_right K Q).trans hk
  have hsum : (2 : Real) / epsilon + 3 / delta < k := hQ.trans_le hQk
  have heRatio : (2 : Real) / epsilon < k := by linarith
  have hdRatio : (3 : Real) / delta < k := by linarith
  have cancel : forall a b : Real, Not (b = 0) -> (a / b) * b = a := by
    intro a b hb
    field_simp
  have heMul := mul_lt_mul_of_pos_right heRatio he
  rw [cancel 2 epsilon (ne_of_gt he)] at heMul
  have hdMul := mul_lt_mul_of_pos_right hdRatio hd
  rw [cancel 3 delta (ne_of_gt hd)] at hdMul
  have heBound : (2 : Real) <= epsilon * k := by nlinarith
  have hdBound : (3 : Real) <= delta * k := by nlinarith
  refine And.intro (upperCutoffIndex_le_doubleExp epsilon k he.le heBound) ?_
  intro i hi
  have hp := upperCutoff_prime_gt_two epsilon k i hi
  have hn : 2 <= PrimeFactorUnimodality.primeAt i - 1 := by omega
  have hscale := upperCutoff_loglog epsilon k i hi
  have hcontrols := hK.2 k hkOriginal (PrimeFactorUnimodality.primeAt i - 1) hn hscale
  have hrestore : PrimeFactorUnimodality.primeAt i - 1 + 1 =
      PrimeFactorUnimodality.primeAt i := Nat.sub_add_cancel (by omega)
  rw [hrestore] at hcontrols
  have hinverse := upperCutoff_reciprocal_lt epsilon delta k i he.le hd hdBound hi
  have hmargin : B < 3 - 1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) := by
    dsimp only [delta] at hinverse
    linarith
  exact And.intro
    (ordinary_density_lt_of_real_ratio k i hkTwo hp hcontrols.2.2.2.2
      (hcontrols.2.1.trans_lt hcontrols.2.2.1))
    (genericOdd_density_lt_of_real_ratio k i B hkTwo hp hcontrols.2.2.2.1
      hcontrols.1 hmargin)

end PrimeFactorOscillations
