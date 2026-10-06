/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.TwinCutoffBounds
import PrimeFactorOscillations.Proof.Upper.GapScaleCutoff

/-!
# Last Twin Transfer

Maintained implementation of the conditional last-ascent location argument.
The arithmetic coverage assumptions remain explicit; no conjecture is an axiom.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

noncomputable section

def IsTwinStep (i : Nat) : Prop :=
  PrimeFactorUnimodality.primeAt (i + 1) = PrimeFactorUnimodality.primeAt i + 2

/-- The bound is on the lower twin member; the upper prime may exceed it. -/
def lastTwinIndex (C : Nat) : Nat := sSup {i | i <= C /\ IsTwinStep i}

private theorem lastTwinIndex_greatest_ascent (f : Nat -> Rat) (C t : Nat)
    (htC : t <= C) (htwin : IsTwinStep t)
    (hallowed : forall j : Nat, t <= j -> j <= C -> IsTwinStep j -> f j < f (j + 1))
    (hnecessary : forall j : Nat, t <= j -> f j < f (j + 1) -> j <= C /\ IsTwinStep j) :
    IsGreatest {i | f i < f (i + 1)} (lastTwinIndex C) := by
  have hbound : BddAbove {i | i <= C /\ IsTwinStep i} :=
    Exists.intro C (fun i hi => hi.1)
  have hne : Set.Nonempty {i | i <= C /\ IsTwinStep i} :=
    Exists.intro t (And.intro htC htwin)
  have hlast : lastTwinIndex C <= C /\ IsTwinStep (lastTwinIndex C) :=
    Nat.sSup_mem hne hbound
  have htlast : t <= lastTwinIndex C := le_csSup hbound (And.intro htC htwin)
  refine And.intro (hallowed _ htlast hlast.1 hlast.2) ?_
  intro j hj
  by_cases hsmall : j <= t
  next => exact hsmall.trans htlast
  next =>
    have h := hnecessary j (Nat.le_of_lt (Nat.lt_of_not_ge hsmall)) hj
    exact le_csSup hbound h

/-- Once a common sufficiently late allowed twin is present, the actual last
ascent in each family is exactly its last twin below its own strict cutoff.
The only extra premise is the explicitly named twin anchor, not a conclusion
about last ascents or an unproved analytic inequality. -/
theorem both_last_ascents_are_last_twins_of_late_anchor (b : Real)
    (hb : (1 : Real) / 5 < b) :
    exists K Q : Nat, 4 <= K /\ 3 <= Q /\ forall k : Nat, K <= k ->
      forall t : Nat, Q <= PrimeFactorUnimodality.primeAt t ->
      b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt t - 1 : Nat)) ->
      IsTwinStep t -> ordinaryTwinPotential k t -> genericTwinPotential k t ->
      IsGreatest {i | ordinaryDensity k i < ordinaryDensity k (i + 1)}
        (lastTwinIndex (ordinaryTwinCutoffIndex k)) /\
      IsGreatest {i | genericOddDensity k i < genericOddDensity k (i + 1)}
        (lastTwinIndex (genericTwinCutoffIndex k)) := by
  choose Kc hc using both_twin_cutoff_eventually_spec
  choose Ks Q hs using ascent_above_one_fifth_forces_twins b hb
  refine Exists.intro (max Kc Ks) (Exists.intro Q
    (And.intro (hc.1.trans (le_max_left _ _)) (And.intro hs.2.1 ?_)))
  intro k hk t htQ htscale htwin hpotO hpotG
  have hk4 : 4 <= k := hc.1.trans ((le_max_left _ _).trans hk)
  have hcut := hc.2 k ((le_max_left _ _).trans hk)
  have hpt : 2 < PrimeFactorUnimodality.primeAt t := hpotO.1
  have hprime_mono : forall j : Nat, t <= j ->
      PrimeFactorUnimodality.primeAt t <= PrimeFactorUnimodality.primeAt j :=
    fun j hj => PrimeFactorUnimodality.primeAt_strictMono.monotone hj
  have hforced : forall j : Nat, t <= j ->
      (ordinaryDensity k j < ordinaryDensity k (j + 1) \/
        genericOddDensity k j < genericOddDensity k (j + 1)) -> IsTwinStep j := by
    intro j htj hj
    have hpj := hprime_mono j htj
    have hsub : PrimeFactorUnimodality.primeAt t - 1 <=
        PrimeFactorUnimodality.primeAt j - 1 := Nat.sub_le_sub_right hpj 1
    have htone : (1 : Real) < (PrimeFactorUnimodality.primeAt t - 1 : Nat) := by
      exact_mod_cast (show 1 < PrimeFactorUnimodality.primeAt t - 1 by omega)
    have hlog := Real.log_le_log (lt_trans (by norm_num) htone)
      (show ((PrimeFactorUnimodality.primeAt t - 1 : Nat) : Real) <=
        (PrimeFactorUnimodality.primeAt j - 1 : Nat) by exact_mod_cast hsub)
    have hloglog := Real.log_le_log (Real.log_pos htone) hlog
    exact hs.2.2 k ((le_max_right _ _).trans hk) j (htQ.trans hpj)
      (htscale.trans hloglog) hj
  have hsupportO : forall j : Nat, t <= j ->
      0 < finiteLocalMass (fun p => 1 / (p : Rat))
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt j)) (k - 1) :=
    fun j hj => (localPrimeRatio_antitone_from _ ordinaryEta_prime_probabilities
      (k - 1) t j (by omega) hj hpotO.2.1).1
  have hsupportG : forall j : Nat, t <= j ->
      0 < finiteLocalMass genericOddEta
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt j)) (k - 1) :=
    fun j hj => (localPrimeRatio_antitone_from _ genericOddEta_prime_probabilities
      (k - 1) t j (by omega) hj hpotG.2.1).1
  constructor
  next =>
    apply lastTwinIndex_greatest_ascent (ordinaryDensity k) (ordinaryTwinCutoffIndex k) t
      (hcut.1.2 t hpotO) htwin
    next =>
      intro j htj hjC hjTwin
      have hpj := hpt.trans_le (hprime_mono j htj)
      have hratio := ordinary_twin_potential_initial_segment
        (k - 1) j (ordinaryTwinCutoffIndex k) (by omega) hjC (hsupportO j htj) hcut.1.1.2.2
      exact (ordinary_twin_ascent_iff k j (by omega) hpj (hsupportO j htj) hjTwin).mpr hratio
    next =>
      intro j htj hascent
      have hpj := hpt.trans_le (hprime_mono j htj)
      have hratio := ordinary_ascent_implies_twin_potential k j (by omega)
        hpj (hsupportO j htj) hascent
      exact And.intro
        (hcut.1.2 j (And.intro hpj (And.intro (hsupportO j htj) hratio)))
        (hforced j htj (Or.inl hascent))
  next =>
    apply lastTwinIndex_greatest_ascent (genericOddDensity k) (genericTwinCutoffIndex k) t
      (hcut.2.2 t hpotG) htwin
    next =>
      intro j htj hjC hjTwin
      have hpj := hpt.trans_le (hprime_mono j htj)
      have hratio := generic_twin_potential_initial_segment
        (k - 1) j (genericTwinCutoffIndex k) (by omega) hjC hpj
        (hsupportG j htj) hcut.2.1.2.2
      exact (generic_twin_ascent_iff k j (by omega) hpj (hsupportG j htj) hjTwin).mpr hratio
    next =>
      intro j htj hascent
      have hpj := hpt.trans_le (hprime_mono j htj)
      have hratio := generic_ascent_implies_twin_potential k j (by omega)
        hpj (hsupportG j htj) hascent
      exact And.intro
        (hcut.2.2 j (And.intro hpj (And.intro (hsupportG j htj) hratio)))
        (hforced j htj (Or.inr hascent))

end
end PrimeFactorOscillations
