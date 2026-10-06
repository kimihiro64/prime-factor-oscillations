/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Order.WellFounded
import PrimeFactorOscillations.Assembly.ConditionalLocation.TwinCutoffExistence

/-!
# Twin Cutoff Bounds

Maintained implementation of the conditional last-ascent location argument.
The arithmetic coverage assumptions remain explicit; no conjecture is an axiom.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- Potential twin ascents themselves stop above every fixed scale b>1/3.
No assertion about the actual following prime gap enters this bound. -/
theorem both_twin_potential_excluded_above_scale (b : Real) (hb : (1 : Real) / 3 < b) :
    exists K Q : Nat, 2 <= K /\ 3 <= Q /\ forall k : Nat, K <= k ->
      forall i : Nat, Q <= PrimeFactorUnimodality.primeAt i ->
      b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) ->
      Not (ordinaryTwinPotential k i) /\ Not (genericTwinPotential k i) := by
  let a := ((1 : Real) / 3 + b) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a]; linarith
  have hba : (1 : Real) / 3 < a := by dsimp [a]; linarith
  have hinv : 1 / a < 3 := by
    have h := one_div_lt_one_div_of_lt (show (0 : Real) < 1 / 3 by norm_num) hba
    norm_num at h
    simpa only [one_div] using h
  let delta := 3 - 1 / a
  have hd : 0 < delta := by dsimp [delta]; linarith
  choose K hK using both_ratios_eventually_below_of_scale a b ha hab
  choose Q hQ using exists_nat_gt (max (3 : Real) (2 + 1 / delta))
  have hQthree : (3 : Real) < Q := (le_max_left _ _).trans_lt hQ
  have hQnat : 3 <= Q := by exact_mod_cast hQthree.le
  refine Exists.intro K (Exists.intro Q (And.intro hK.1 (And.intro hQnat ?_)))
  intro k hk i hp hscale
  have hk2 : 2 <= k := hK.1.trans hk
  have hpgt : 2 < PrimeFactorUnimodality.primeAt i := by omega
  have hpR : (Q : Real) <= PrimeFactorUnimodality.primeAt i := by exact_mod_cast hp
  have hlarge : 1 / delta < (PrimeFactorUnimodality.primeAt i : Real) - 2 := by
    have h := (le_max_right _ _).trans_lt hQ
    linarith only [h, hpR]
  have hcorrection : 1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) < delta := by
    have h := one_div_lt_one_div_of_lt (div_pos (by norm_num) hd) hlarge
    have hc : (1 : Real) / (1 / delta) = delta := by field_simp
    rwa [hc] at h
  have hlowRat := genericOdd_threshold_lower (PrimeFactorUnimodality.primeAt i)
    (PrimeFactorUnimodality.primeAt i + 2) hpgt (le_refl _)
  rw [generic_twin_threshold_exact _ hpgt] at hlowRat
  have hlow : (3 : Real) - 1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) <=
      (genericTwinThreshold (PrimeFactorUnimodality.primeAt i) : Real) := by
    exact_mod_cast hlowRat
  have hmargin : 1 / a <
      (genericTwinThreshold (PrimeFactorUnimodality.primeAt i) : Real) := by
    dsimp only [delta] at hcorrection
    linarith only [hcorrection, hlow]
  have hr := hK.2 k hk (PrimeFactorUnimodality.primeAt i - 1) (by omega) hscale
  rw [Nat.sub_add_cancel (show 1 <= PrimeFactorUnimodality.primeAt i by omega)] at hr
  have hsub : k - 1 - 1 = k - 2 := by omega
  constructor
  next =>
    intro hpot
    have h := hpot.2.2
    rw [ordinary_localPrimeRatio_eq] at h
    have hreal : (3 : Real) < (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i))
        (k - 1) : Real) := by exact_mod_cast h
    exact (not_lt_of_ge (hr.2.1.trans hinv.le)) hreal
  next =>
    intro hpot
    have h := hpot.2.2
    unfold localPrimeRatio at h
    rw [hsub] at h
    have hreal := (Rat.cast_lt (K := Real)).mpr h
    exact (not_lt_of_ge (hr.1.trans hmargin.le)) hreal

private theorem log_log_ge_of_double_exp_le (t x : Real)
    (hx : Real.exp (Real.exp t) <= x) : t <= Real.log (Real.log x) := by
  have h := Real.log_le_log (Real.exp_pos (Real.exp t)) hx
  rw [Real.log_exp] at h
  have hh := Real.log_le_log (Real.exp_pos t) h
  simpa only [Real.log_exp] using hh

theorem both_twin_potential_eventually_bddAbove :
    exists K : Nat, 2 <= K /\ forall k : Nat, K <= k ->
      BddAbove {i | ordinaryTwinPotential k i} /\
        BddAbove {i | genericTwinPotential k i} := by
  choose K Q h using both_twin_potential_excluded_above_scale 1 (by norm_num)
  refine Exists.intro K (And.intro h.1 ?_)
  intro k hk
  let B := max Q (Nat.ceil (Real.exp (Real.exp (k : Real))) + 3)
  have htail : forall i : Nat, B < i ->
      Not (ordinaryTwinPotential k i) /\ Not (genericTwinPotential k i) := by
    intro i hi
    have hidx : i <= PrimeFactorUnimodality.primeAt i :=
      PrimeFactorUnimodality.primeAt_strictMono.id_le i
    have hQ : Q <= PrimeFactorUnimodality.primeAt i :=
      (le_max_left _ _).trans (hi.le.trans hidx)
    have hceil : Nat.ceil (Real.exp (Real.exp (k : Real))) <=
        PrimeFactorUnimodality.primeAt i - 1 := by
      have hB := le_max_right Q (Nat.ceil (Real.exp (Real.exp (k : Real))) + 3)
      omega
    have hscale := log_log_ge_of_double_exp_le (k : Real)
      (PrimeFactorUnimodality.primeAt i - 1 : Nat)
      ((Nat.le_ceil _).trans (by exact_mod_cast hceil))
    exact h.2.2 k hk i hQ (by simpa only [one_mul] using hscale)
  constructor
  next =>
    refine Exists.intro B ?_
    intro i hi
    by_contra hn
    exact (htail i (Nat.lt_of_not_ge hn)).1 hi
  next =>
    refine Exists.intro B ?_
    intro i hi
    by_contra hn
    exact (htail i (Nat.lt_of_not_ge hn)).2 hi

/-- Both canonical strict twin criteria have actual attained finite maxima. -/
theorem both_twin_cutoff_eventually_spec :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k ->
      (ordinaryTwinPotential k (ordinaryTwinCutoffIndex k) /\
        forall i : Nat, ordinaryTwinPotential k i -> i <= ordinaryTwinCutoffIndex k) /\
      (genericTwinPotential k (genericTwinCutoffIndex k) /\
        forall i : Nat, genericTwinPotential k i -> i <= genericTwinCutoffIndex k) := by
  choose Ks hs using both_twin_potential_seed ((1 : Real) / 4) (by norm_num) (by norm_num)
  choose Kb hb using both_twin_potential_eventually_bddAbove
  refine Exists.intro (max Ks Kb) (And.intro (hs.1.trans (le_max_left _ _)) ?_)
  intro k hk
  choose i hi using hs.2 k ((le_max_left _ _).trans hk)
  have hbound := hb.2 k ((le_max_right _ _).trans hk)
  have hneO : Set.Nonempty {i | ordinaryTwinPotential k i} := Exists.intro i hi.2.2.1
  have hneG : Set.Nonempty {i | genericTwinPotential k i} := Exists.intro i hi.2.2.2
  exact And.intro
    (And.intro (Nat.sSup_mem hneO hbound.1) (fun j hj => le_csSup hbound.1 hj))
    (And.intro (Nat.sSup_mem hneG hbound.2) (fun j hj => le_csSup hbound.2 hj))

end PrimeFactorOscillations
