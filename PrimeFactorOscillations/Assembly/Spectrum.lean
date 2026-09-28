import PrimeFactorOscillations.Assembly.Headline
import PrimeFactorOscillations.Proof.Lower.SpectrumRate
import PrimeFactorOscillations.Proof.Upper.SpectrumRate

/-! # Exact prime-gap frequency spectrum for the canonical reversal numbers -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- Any eventual choice of the attained maximal count for either canonical
family has exactly the actual prime-gap frequency spectrum as its upper rate.
The family may even vary with the rank. -/
theorem canonical_reversal_limsup_eq_spectrum
    (n : Nat -> Nat)
    (hn : exists K : Nat, forall k : Nat, K <= k ->
      HasReversalNumber (ordinaryDensity k) (n k) \/
        HasReversalNumber (genericOddDensity k) (n k)) :
    Filter.limsup (fun k : Nat =>
      Real.log (Real.log (3 + (n k : Real))) / k) Filter.atTop = primeGapSpectrum 1 := by
  choose Kn hKn using hn
  have hfamily : exists K : Nat, forall k : Nat, K <= k ->
      HasAtLeastReversals (ordinaryDensity k) (n k) \/
        HasAtLeastReversals (genericOddDensity k) (n k) := by
    refine Exists.intro Kn ?_
    intro k hk
    exact (hKn k hk).imp (fun h => h.1) (fun h => h.1)
  have hupper := canonical_reversal_limsup_le_spectrum n hfamily
  let S := primeGapSpectrum 1
  have hS : 0 <= S := (primeGapSpectrum_bounds 1 (by norm_num)).1
  choose KU hKU using both_reversal_counts_eventually_le_spectrum (S + 1) (by dsimp only [S]; linarith)
  choose KC hKC using Real.eventually_mul_double_exp_add_one_le (S + 1) (S + 2) 4
    (by linarith) (by linarith) (by norm_num)
  have hmodel : exists A : Real, exists K : Nat, forall k : Nat, K <= k ->
      3 + (n k : Real) <= Real.exp (Real.exp (A * (k : Real))) := by
    refine Exists.intro (S + 2) (Exists.intro (max Kn (max KU KC)) ?_)
    intro k hk
    have hactual := (hKn k (by omega)).imp (fun h => h.1) (fun h => h.1)
    have hnu := hKU k (by omega) (n k) hactual
    have hc := hKC k (by omega)
    have hE := Real.exp_pos (Real.exp ((S + 1) * k))
    linarith only [hnu, hc, hE]
  have ht : exists K : Nat, forall k : Nat, K <= k -> (1 : Real) <= k :=
    Exists.intro 1 (fun k hk => by exact_mod_cast hk)
  let R := Filter.limsup (fun k : Nat =>
    Real.log (Real.log (3 + (n k : Real))) / k) Filter.atTop
  have hnonneg : 0 <= R := by
    apply (Real.le_limsup_log_log_div_gauge_iff (fun k => (n k : Real))
      (fun k : Nat => (k : Real)) (fun k => Nat.cast_nonneg _) ht hmodel 0).mpr
    intro a ha K
    choose M hM using exists_nat_gt ((Real.log (Real.log 2) - 1) / a)
    let k := max K M
    have hkM : (M : Real) <= k := by exact_mod_cast le_max_right K M
    have hm := mul_le_mul_of_nonpos_left (hM.le.trans hkM) ha.le
    have hc : a * ((Real.log (Real.log 2) - 1) / a) =
        Real.log (Real.log 2) - 1 := by field_simp [ne_of_lt ha]
    rw [hc] at hm
    have hsmall : a * k < Real.log (Real.log 2) := by linarith
    have he := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr hsmall)
    rw [Real.exp_log (Real.log_pos (by norm_num : (1 : Real) < 2)),
      Real.exp_log (by norm_num : (0 : Real) < 2)] at he
    refine Exists.intro k (And.intro (le_max_left K M) ?_)
    exact he.trans (show (2 : Real) < 3 + (n k : Real) by
      have hn0 : (0 : Real) <= n k := Nat.cast_nonneg (n k)
      linarith only [hn0])
  have hlower : forall H : Nat, primeGapFrequencyExponent H / ((H : Real) + 1) <= R := by
    intro H
    let L := primeGapFrequencyExponent H / ((H : Real) + 1)
    by_cases hL : 0 < L
    next =>
      apply (Real.le_limsup_log_log_div_gauge_iff (fun k => (n k : Real))
        (fun k : Nat => (k : Real)) (fun k => Nat.cast_nonneg _) ht hmodel L).mpr
      intro a ha K
      have hmax : max 0 a < L := max_lt_iff.mpr (And.intro hL ha)
      choose c hc using exists_between hmax
      have hcpos : 0 < c := (le_max_left 0 a).trans_lt hc.1
      have hac : a < c := (le_max_right 0 a).trans_lt hc.1
      choose k hk using both_frequently_reversal_supply_below_gap_exponent H c hcpos hc.2
        (max K Kn)
      choose m hm using hk.2
      have hmn : m <= n k := by
        rcases hKn k ((le_max_right K Kn).trans hk.1) with ho | hg
        next => exact ho.2 m hm.2.1
        next => exact hg.2 m hm.2.2
      have hcoef := mul_le_mul_of_nonneg_right hac.le (Nat.cast_nonneg k : (0 : Real) <= k)
      have he := (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hcoef)).trans hm.1
      have hmR : (m : Real) <= n k := by exact_mod_cast hmn
      refine Exists.intro k (And.intro ((le_max_left K Kn).trans hk.1) ?_)
      linarith only [he, hmR]
    next =>
      exact (le_of_not_gt hL).trans hnonneg
  apply le_antisymm hupper
  change sSup (Set.range (fun j : Nat =>
    primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + 1))) <= R
  apply csSup_le (Set.range_nonempty _)
  intro x hx
  choose j hj using hx
  rw [<- hj]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hlower (j + 2)

/-- Both canonical families have attained finite maximal-count sequences with
the exact common spectrum. Values at finitely many early ranks are immaterial.
All existence inputs are supplied by the maintained unconditional theorem. -/
theorem exists_canonical_sharp_reversal_rates :
    exists nOrd nGen : Nat -> Nat,
      (exists K : Nat, forall k : Nat, K <= k ->
        HasReversalNumber (ordinaryDensity k) (nOrd k) /\
          HasReversalNumber (genericOddDensity k) (nGen k)) /\
      Filter.limsup (fun k : Nat =>
        Real.log (Real.log (3 + (nOrd k : Real))) / k) Filter.atTop = primeGapSpectrum 1 /\
      Filter.limsup (fun k : Nat =>
        Real.log (Real.log (3 + (nGen k : Real))) / k) Filter.atTop = primeGapSpectrum 1 := by
  classical
  choose a ha using doubleExponentialReversalBounds
  choose K hK using ha.2 1 (by norm_num)
  let nOrd := fun k : Nat => if hk : K <= k then Classical.choose (hK.2 k hk).1 else 0
  let nGen := fun k : Nat => if hk : K <= k then Classical.choose (hK.2 k hk).2 else 0
  have hOrd : forall k : Nat, K <= k -> HasReversalNumber (ordinaryDensity k) (nOrd k) := by
    intro k hk
    dsimp only [nOrd]
    rw [dite_eq_left hk]
    exact (Classical.choose_spec (hK.2 k hk).1).1
  have hGen : forall k : Nat, K <= k -> HasReversalNumber (genericOddDensity k) (nGen k) := by
    intro k hk
    dsimp only [nGen]
    rw [dite_eq_left hk]
    exact (Classical.choose_spec (hK.2 k hk).2).1
  have hEqOrd := canonical_reversal_limsup_eq_spectrum nOrd
    (Exists.intro K (fun k hk => Or.inl (hOrd k hk)))
  have hEqGen := canonical_reversal_limsup_eq_spectrum nGen
    (Exists.intro K (fun k hk => Or.inr (hGen k hk)))
  exact Exists.intro nOrd (Exists.intro nGen (And.intro
    (Exists.intro K (fun k hk => And.intro (hOrd k hk) (hGen k hk)))
    (And.intro hEqOrd hEqGen)))

end PrimeFactorOscillations
