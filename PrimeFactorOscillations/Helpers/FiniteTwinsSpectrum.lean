/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.GapSpectrumPhase

/-!
# Finite twins and the full reversal-frequency spectrum

Finite twins force the gap-three exponent to vanish. If the ordinary
spectrum equals1/5, width four must have exponent one and determines
all positive-dimensional spectra. This is a conditional consequence of
the exact spectrum, not a contradiction to RH or a twin-prime proof.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

theorem gapFrequencyExponent_three_eq_zero_of_finite_twins
    (hfinite : exists I : Nat, forall i : Nat, I <= i -> Not (primeGap i = 2)) :
    primeGapFrequencyExponent 3 = 0 := by
  classical
  choose I hI using hfinite
  let B := max I 1
  have hBound : forall X : Nat, primeGapFrequencyCount 3 X <= B := by
    intro X
    let S := (Finset.range X).filter (fun i => primeAt i <= X /\ primeGap i <= 3)
    have hsub : forall i : Nat, Membership.mem S i ->
        Membership.mem (Finset.range B) i := by
      intro i hi
      apply Finset.mem_range.mpr
      by_contra hn
      have hiB : B <= i := Nat.le_of_not_gt hn
      have hiI : I <= i := (le_max_left I 1).trans hiB
      have hiOne : 1 <= i := (le_max_right I 1).trans hiB
      have hbase : i + 2 <= primeAt i := Nat.add_two_le_nth_prime i
      have hp : 2 < primeAt i := by omega
      have hpq : primeAt i < primeAt (i + 1) := primeAt_strictMono (Nat.lt_succ_self i)
      have hq : 2 < primeAt (i + 1) := hp.trans hpq
      have hpodd := (prime_primeAt i).eq_two_or_odd.resolve_left (ne_of_gt hp)
      have hqodd := (prime_primeAt (i + 1)).eq_two_or_odd.resolve_left (ne_of_gt hq)
      have hgap : primeGap i <= 3 := (Finset.mem_filter.mp hi).2.2
      have hnot := hI i hiI
      unfold primeGap at hgap hnot
      omega
    change S.card <= B
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hB : (0 : Real) <= B := Nat.cast_nonneg _
  simpa only [primeGapFrequencyExponent] using
    Real.limsup_log_log_bounded_count_eq_zero
      (fun X => (primeGapFrequencyCount 3 X : Real))
      (fun X => Nat.cast_nonneg _) (B : Real) hB
      (fun X => by exact_mod_cast hBound X)

theorem gapFrequencyExponent_four_eq_one_of_spectrum_fifth
    (hsmall : primeGapFrequencyExponent 3 = 0)
    (hspectrum : primeGapSpectrum 1 = (1 : Real) / 5) :
    primeGapFrequencyExponent 4 = 1 := by
  have hUpper : primeGapSpectrum 1 <= max (primeGapFrequencyExponent 4 / 5) (1 / 6 : Real) := by
    change sSup (Set.range (fun j : Nat =>
      primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + 1))) <= _
    apply csSup_le (Set.range_nonempty _)
    intro v hv
    choose j hj using hv
    rw [<- hj]
    by_cases hjSmall : j + 2 <= 3
    . have hzero : primeGapFrequencyExponent (j + 2) = 0 := by
        have hle := primeGapFrequencyExponent_mono hjSmall
        rw [hsmall] at hle
        exact le_antisymm hle (primeGapFrequencyExponent_bounds _).1
      rw [hzero, zero_div]
      exact (by norm_num : (0 : Real) <= 1 / 6).trans (le_max_right _ _)
    . by_cases hjFour : j + 2 = 4
      . have hjTwo : j = 2 := by omega
        subst j
        norm_num only [Nat.cast_ofNat, show (2 : Real) + 2 + 1 = 5 by norm_num]
        exact le_max_left _ _
      . have hjLarge : 3 <= j := by omega
        have hd : (6 : Real) <= (j : Real) + 2 + 1 := by exact_mod_cast (by omega : 6 <= j + 2 + 1)
        have hratio : primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + 1) <= 1 / 6 := by
          calc
            _ <= 1 / ((j : Real) + 2 + 1) :=
              div_le_div_of_nonneg_right (primeGapFrequencyExponent_bounds _).2 (by positivity)
            _ <= _ := one_div_le_one_div_of_le (by norm_num) hd
        exact hratio.trans (le_max_right _ _)
  by_contra hn
  have hg : primeGapFrequencyExponent 4 < 1 :=
    (lt_or_eq_of_le (primeGapFrequencyExponent_bounds 4).2).resolve_right hn
  have hmax : max (primeGapFrequencyExponent 4 / 5) (1 / 6 : Real) < 1 / 5 :=
    max_lt_iff.mpr (And.intro (by linarith) (by norm_num))
  rw [hspectrum] at hUpper
  exact (not_lt_of_ge hUpper) hmax

theorem primeGapSpectrum_eq_of_first_full_class
    (J : Nat) (hJ : 2 <= J) (hfull : primeGapFrequencyExponent J = 1)
    (hsmall : forall H : Nat, 2 <= H -> H < J -> primeGapFrequencyExponent H = 0)
    (nu : Real) (hnu : 0 < nu) :
    primeGapSpectrum nu = 1 / ((J : Real) + nu) := by
  have hlo := primeGapFrequency_ratio_le_spectrum J nu hnu
  rw [hfull] at hlo
  apply le_antisymm ?_ hlo
  choose H hH using primeGapSpectrum_finite_maximum J hJ hfull nu hnu
  rw [hH.2.2]
  by_cases heq : H = J
  . rw [heq, hfull]
  . rw [hsmall H hH.1 (by omega), zero_div]
    positivity

theorem finite_twins_and_spectrum_fifth_determine_all_spectra
    (hfinite : exists I : Nat, forall i : Nat, I <= i -> Not (primeGap i = 2))
    (hspectrum : primeGapSpectrum 1 = (1 : Real) / 5) :
    primeGapFrequencyExponent 4 = 1 /\
      forall nu : Real, 0 < nu -> primeGapSpectrum nu = 1 / (4 + nu) := by
  have hsmall := gapFrequencyExponent_three_eq_zero_of_finite_twins hfinite
  have hfull := gapFrequencyExponent_four_eq_one_of_spectrum_fifth hsmall hspectrum
  refine And.intro hfull ?_
  intro nu hnu
  apply primeGapSpectrum_eq_of_first_full_class 4 (by omega) hfull _ nu hnu
  intro H _ hH
  have hle := primeGapFrequencyExponent_mono (show H <= 3 by omega)
  rw [hsmall] at hle
  exact le_antisymm hle (primeGapFrequencyExponent_bounds _).1

end PrimeFactorOscillations
