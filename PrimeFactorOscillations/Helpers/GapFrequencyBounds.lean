import PrimeFactorOscillations.Definitions.GapFrequency
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CountingRate

/-! # Checked growth exponents for actual consecutive-prime-gap counts -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

/-- Every actual fixed-gap frequency exponent lies in [0,1]. -/
theorem primeGapFrequencyExponent_bounds (H : Nat) :
    0 <= primeGapFrequencyExponent H /\ primeGapFrequencyExponent H <= 1 := by
  simpa only [primeGapFrequencyExponent] using
    Real.limsup_log_log_linear_count_bounds
      (fun X => (primeGapFrequencyCount H X : Real))
      (fun X => Nat.cast_nonneg _)
      (fun X => by exact_mod_cast primeGapFrequencyCount_le H X)

private theorem primeGapFrequency_upper_model (H : Nat) :
    exists A : Real, exists K : Nat, forall X : Nat, K <= X ->
      3 + (primeGapFrequencyCount H X : Real) <=
        Real.exp (Real.exp (A * Real.log (Real.log (X : Real)))) := by
  exact Exists.intro (2 : Real)
    (Real.eventually_linear_count_le_double_exp_log_log
      (fun X => (primeGapFrequencyCount H X : Real))
      (fun X => Nat.cast_nonneg _)
      (fun X => by exact_mod_cast primeGapFrequencyCount_le H X)
      2 (by norm_num))

/-- Increasing the allowed gap cannot decrease its actual frequency exponent. -/
theorem primeGapFrequencyExponent_mono : Monotone primeGapFrequencyExponent := by
  intro H J hHJ
  have hleft := Real.limsup_log_log_div_gauge_le_iff
    (fun X => (primeGapFrequencyCount H X : Real))
    (fun X : Nat => Real.log (Real.log (X : Real)))
    (fun X => Nat.cast_nonneg _) (Real.eventually_le_log_log_nat 1)
    (primeGapFrequency_upper_model H) (primeGapFrequencyExponent J)
  apply hleft.mpr
  intro b hb
  have hright := Real.limsup_log_log_div_gauge_le_iff
    (fun X => (primeGapFrequencyCount J X : Real))
    (fun X : Nat => Real.log (Real.log (X : Real)))
    (fun X => Nat.cast_nonneg _) (Real.eventually_le_log_log_nat 1)
    (primeGapFrequency_upper_model J) (primeGapFrequencyExponent J)
  have hself : Filter.limsup
      (fun X : Nat => Real.log (Real.log (3 + (primeGapFrequencyCount J X : Real))) /
        Real.log (Real.log (X : Real))) Filter.atTop <= primeGapFrequencyExponent J :=
    le_refl _
  choose K hK using hright.mp hself b hb
  refine Exists.intro K ?_
  intro X hX
  have hcount : (primeGapFrequencyCount H X : Real) <= primeGapFrequencyCount J X := by
    exact_mod_cast primeGapFrequencyCount_mono_gap X hHJ
  have hupper := hK X hX
  linarith only [hcount, hupper]

/-- A gap of size at most one can start only at prime index zero. This keeps
the exceptional initial gap explicit when the sharp envelope sums from zero. -/
theorem primeGapFrequencyCount_le_one_of_small_gap (H X : Nat) (hH : H <= 1) :
    primeGapFrequencyCount H X <= 1 := by
  classical
  let S := (Finset.range X).filter (fun i => primeAt i <= X /\ primeGap i <= H)
  have hsub : forall i : Nat, Membership.mem S i ->
      Membership.mem (Finset.range 1) i := by
    intro i hi
    apply Finset.mem_range.mpr
    by_contra hn
    have hbase : i + 2 <= primeAt i := Nat.add_two_le_nth_prime i
    have hp : 2 < primeAt i := by omega
    have hpq : primeAt i < primeAt (i + 1) :=
      primeAt_strictMono (Nat.lt_succ_self i)
    have hq : 2 < primeAt (i + 1) := hp.trans hpq
    have hpodd := (prime_primeAt i).eq_two_or_odd.resolve_left (ne_of_gt hp)
    have hqodd := (prime_primeAt (i + 1)).eq_two_or_odd.resolve_left (ne_of_gt hq)
    have hgap : primeGap i <= H := (Finset.mem_filter.mp hi).2.2
    change primeAt (i + 1) - primeAt i <= H at hgap
    omega
  change S.card <= 1
  simpa only [Finset.card_range] using Finset.card_le_card hsub

/-- The artificial gap classes zero and one contribute zero exponent. -/
theorem primeGapFrequencyExponent_eq_zero_of_small_gap (H : Nat) (hH : H <= 1) :
    primeGapFrequencyExponent H = 0 := by
  simpa only [primeGapFrequencyExponent] using
    Real.limsup_log_log_bounded_count_eq_zero
      (fun X => (primeGapFrequencyCount H X : Real))
      (fun X => Nat.cast_nonneg _) 1 (by norm_num)
      (fun X => by exact_mod_cast primeGapFrequencyCount_le_one_of_small_gap H X hH)

end PrimeFactorOscillations
