import PrimeFactorOscillations.Proof.Lower.ReciprocalSmoothRate
import PrimeFactorOscillations.Proof.Upper.ReciprocalSmoothAllRanks
import PrimeFactorOscillations.Proof.Upper.ReciprocalSmoothFiniteMaximum
import PrimeFactorOscillations.Proof.Upper.ReciprocalSmoothSpectrumRate

/-! # Exact prime-gap frequency spectrum for the reciprocal-smooth reversal numbers -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

/-- Every eventual choice of actual maximal reversal counts for a fixed
reciprocal-smooth law has exactly the prime-gap frequency spectrum at nu. -/
theorem reversal_limsup_eq_spectrum
    (law : ReciprocalSmoothLaw) (n : Nat -> Nat)
    (hn : exists K : Nat, forall k : Nat, K <= k ->
      HasReversalNumber (law.rankDensity k) (n k)) :
    Filter.limsup (fun k : Nat =>
      Real.log (Real.log (3 + (n k : Real))) / k) Filter.atTop = primeGapSpectrum law.nu := by
  choose Kn hKn using hn
  have hfamily : exists K : Nat, forall k : Nat, K <= k ->
      HasAtLeastReversals (law.rankDensity k) (n k) := by
    refine Exists.intro Kn ?_
    intro k hk
    exact (hKn k hk).1
  have hupper := law.reversal_limsup_le_spectrum n hfamily
  let S := primeGapSpectrum law.nu
  have hS : 0 <= S := (primeGapSpectrum_bounds law.nu law.nu_pos).1
  choose KU hKU using law.reversal_counts_eventually_le_spectrum (S + 1) (by dsimp only [S]; linarith)
  choose KC hKC using Real.eventually_mul_double_exp_add_one_le (S + 1) (S + 2) 4
    (by linarith) (by linarith) (by norm_num)
  have hmodel : exists A : Real, exists K : Nat, forall k : Nat, K <= k ->
      3 + (n k : Real) <= Real.exp (Real.exp (A * (k : Real))) := by
    refine Exists.intro (S + 2) (Exists.intro (max Kn (max KU KC)) ?_)
    intro k hk
    have hactual := (hKn k (by omega)).1
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
  have hlower : forall H : Nat, primeGapFrequencyExponent H / ((H : Real) + law.nu) <= R := by
    intro H
    let L := primeGapFrequencyExponent H / ((H : Real) + law.nu)
    by_cases hL : 0 < L
    next =>
      apply (Real.le_limsup_log_log_div_gauge_iff (fun k => (n k : Real))
        (fun k : Nat => (k : Real)) (fun k => Nat.cast_nonneg _) ht hmodel L).mpr
      intro a ha K
      have hmax : max 0 a < L := max_lt_iff.mpr (And.intro hL ha)
      choose c hc using exists_between hmax
      have hcpos : 0 < c := (le_max_left 0 a).trans_lt hc.1
      have hac : a < c := (le_max_right 0 a).trans_lt hc.1
      choose k hk using law.frequently_reversal_supply_below_gap_exponent H c hcpos hc.2
        (max K Kn)
      choose m hm using hk.2
      have hmn : m <= n k := by
        exact (hKn k ((le_max_right K Kn).trans hk.1)).2 m hm.2
      have hcoef := mul_le_mul_of_nonneg_right hac.le (Nat.cast_nonneg k : (0 : Real) <= k)
      have he := (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hcoef)).trans hm.1
      have hmR : (m : Real) <= n k := by exact_mod_cast hmn
      refine Exists.intro k (And.intro ((le_max_left K Kn).trans hk.1) ?_)
      linarith only [he, hmR]
    next =>
      exact (le_of_not_gt hL).trans hnonneg
  apply le_antisymm hupper
  change sSup (Set.range (fun j : Nat =>
    primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + law.nu))) <= R
  apply csSup_le (Set.range_nonempty _)
  intro x hx
  choose j hj using hx
  rw [<- hj]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hlower (j + 2)

/-- Actual finite maximal reversal numbers exist on a rank tail and attain
the sharp gap spectrum. Finitely many early ranks can be assigned arbitrarily. -/
theorem exists_sharp_reversal_rate (law : ReciprocalSmoothLaw) :
    exists n : Nat -> Nat,
      (exists K : Nat, forall k : Nat, K <= k ->
        HasReversalNumber (law.rankDensity k) (n k)) /\
      Filter.limsup (fun k : Nat =>
        Real.log (Real.log (3 + (n k : Real))) / k) Filter.atTop =
        primeGapSpectrum law.nu := by
  classical
  choose K hK using Filter.eventually_atTop.mp law.eventually_exists_reversal_number
  let n := fun k : Nat => if hk : K <= k then Classical.choose (hK k hk) else 0
  have hn : forall k : Nat, K <= k -> HasReversalNumber (law.rankDensity k) (n k) := by
    intro k hk
    dsimp only [n]
    rw [dite_eq_left hk]
    exact Classical.choose_spec (hK k hk)
  exact Exists.intro n (And.intro (Exists.intro K hn)
    (law.reversal_limsup_eq_spectrum n (Exists.intro K hn)))

/-- Actual finite maximal reversal counts exist at every rank and have the
sharp spectrum; no arbitrary assignment at small ranks is needed. -/
theorem exists_sharp_reversal_rate_all_ranks (law : ReciprocalSmoothLaw) :
    exists n : Nat -> Nat,
      (forall k : Nat, HasReversalNumber (law.rankDensity k) (n k)) /\
      Filter.limsup (fun k : Nat =>
        Real.log (Real.log (3 + (n k : Real))) / k) Filter.atTop =
        primeGapSpectrum law.nu := by
  choose n hn using law.exists_reversal_number_all_ranks
  exact Exists.intro n (And.intro hn (law.reversal_limsup_eq_spectrum n
    (Exists.intro 0 (fun k _ => hn k))))


end PrimeFactorOscillations.ReciprocalSmoothLaw
