import PrimeFactorOscillations.Definitions.GapSpectrum
import PrimeFactorOscillations.Helpers.GapFrequencyBounds

/-! # Bounds for the prime-gap frequency spectrum -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

noncomputable section

private theorem spectrum_term_bounds (j : Nat) (nu : Real) (hnu : 0 < nu) :
    0 <= primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + nu) /\
      primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + nu) <= 1 / (2 + nu) := by
  have hgamma := primeGapFrequencyExponent_bounds (j + 2)
  have hd : 0 < (j : Real) + 2 + nu := by positivity
  have hb : 0 < (2 : Real) + nu := by positivity
  have hnonneg := div_nonneg hgamma.1 hd.le
  refine And.intro hnonneg ?_
  have hc : (primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + nu)) *
      ((j : Real) + 2 + nu) = primeGapFrequencyExponent (j + 2) := by
    field_simp [ne_of_gt hd]
  have hcost := mul_nonneg hnonneg (Nat.cast_nonneg j : (0 : Real) <= j)
  have hprod : (primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + nu)) *
      (2 + nu) <= 1 := by nlinarith only [hc, hcost, hgamma.2]
  have hi : (1 / (2 + nu)) * (2 + nu) = (1 : Real) := by
    field_simp [ne_of_gt hb]
  by_contra hn
  have hgt : 1 / (2 + nu) <
      primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + nu) := lt_of_not_ge hn
  have hm := mul_lt_mul_of_pos_right hgt hb
  rw [hi] at hm
  exact (not_lt_of_ge hprod) hm

private theorem spectrum_range_bddAbove (nu : Real) (hnu : 0 < nu) :
    BddAbove (Set.range (fun j : Nat =>
      primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + nu))) := by
  refine Exists.intro (1 / (2 + nu)) ?_
  intro x hx
  choose j hj using hx
  rw [<- hj]
  exact (spectrum_term_bounds j nu hnu).2

/-- The spectrum is a genuine bounded real quantity, between zero and the
smallest possible odd-prime-gap scale. -/
theorem primeGapSpectrum_bounds (nu : Real) (hnu : 0 < nu) :
    0 <= primeGapSpectrum nu /\ primeGapSpectrum nu <= 1 / (2 + nu) := by
  have hbdd := spectrum_range_bddAbove nu hnu
  have hzero : primeGapFrequencyExponent (0 + 2) / (((0 : Nat) : Real) + 2 + nu) <=
      primeGapSpectrum nu := le_csSup hbdd (Exists.intro (0 : Nat) (by simp))
  refine And.intro ((spectrum_term_bounds 0 nu hnu).1.trans hzero) ?_
  apply csSup_le (Set.range_nonempty _)
  intro x hx
  choose j hj using hx
  rw [<- hj]
  exact (spectrum_term_bounds j nu hnu).2

/-- Every genuine gap class lies below the spectrum at its own denominator. -/
theorem primeGapFrequency_ratio_le_spectrum_of_two_le
    (H : Nat) (nu : Real) (hH : 2 <= H) (hnu : 0 < nu) :
    primeGapFrequencyExponent H / ((H : Real) + nu) <= primeGapSpectrum nu := by
  have hj : H - 2 + 2 = H := Nat.sub_add_cancel hH
  have hjR : ((H - 2 : Nat) : Real) + 2 = (H : Real) := by exact_mod_cast hj
  have h : primeGapFrequencyExponent (H - 2 + 2) /
      (((H - 2 : Nat) : Real) + 2 + nu) <= primeGapSpectrum nu :=
    le_csSup (spectrum_range_bddAbove nu hnu) (Set.mem_range_self (H - 2))
  rw [hj, hjR] at h
  exact h

/-- The artificial initial gap classes also obey the bound because their
frequency exponents are zero. This matches the finite envelope's full sum. -/
theorem primeGapFrequency_ratio_le_spectrum
    (H : Nat) (nu : Real) (hnu : 0 < nu) :
    primeGapFrequencyExponent H / ((H : Real) + nu) <= primeGapSpectrum nu := by
  by_cases hH : 2 <= H
  next => exact primeGapFrequency_ratio_le_spectrum_of_two_le H nu hH hnu
  next =>
    rw [primeGapFrequencyExponent_eq_zero_of_small_gap H (by omega), zero_div]
    exact (primeGapSpectrum_bounds nu hnu).1

/-- The canonical spectrum has the universal upper endpoint one third. -/
theorem primeGapSpectrum_one_le_one_third :
    primeGapSpectrum 1 <= (1 : Real) / 3 := by
  simpa only [show (2 : Real) + 1 = 3 by norm_num] using
    (primeGapSpectrum_bounds 1 (by norm_num)).2

end

end PrimeFactorOscillations
