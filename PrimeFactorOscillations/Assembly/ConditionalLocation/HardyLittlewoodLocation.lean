/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.TwinCoverageIdentification

/-!
# Hardy Littlewood Location

Maintained implementation of the conditional last-ascent location argument.
The arithmetic coverage assumptions remain explicit; no conjecture is an axiom.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

noncomputable section

/-- The lower prime at the supremum of the actual ascent indices.
Theorems below prove that the supremum is attained for all large ranks. -/
def lastAscentPrime (f : Nat -> Rat) : Nat :=
  PrimeFactorUnimodality.primeAt (sSup {i | f i < f (i + 1)})

theorem lastTwinIndex_eventually_relative (hcoverage : MultiplicativeTwinCoverage)
    (eps : Real) (heps : 0 < eps) (heps1 : eps < 1) :
    exists X : Real, forall C : Nat,
      X <= (PrimeFactorUnimodality.primeAt C : Real) ->
      (1 - eps) * (PrimeFactorUnimodality.primeAt C : Real) <
        PrimeFactorUnimodality.primeAt (lastTwinIndex C) /\
      PrimeFactorUnimodality.primeAt (lastTwinIndex C) <= PrimeFactorUnimodality.primeAt C := by
  choose X hX using hcoverage eps heps heps1
  have hd : 0 < 1 - eps := sub_pos.mpr heps1
  refine Exists.intro (max X (3 / (1 - eps))) ?_
  intro C hC
  have hCX := (le_max_left _ _).trans hC
  have hCd := (le_max_right _ _).trans hC
  have hmul := mul_le_mul_of_nonneg_left hCd hd.le
  have hc : (1 - eps) * (3 / (1 - eps)) = 3 := by field_simp
  rw [hc] at hmul
  choose p hp using hX (PrimeFactorUnimodality.primeAt C) hCX
  have hpgt : 2 < p := by
    have h : (2 : Real) < p := by linarith only [hmul, hp.2.2.1]
    exact_mod_cast h
  let i := Nat.count Nat.Prime p
  have hi : PrimeFactorUnimodality.primeAt i = p := Nat.nth_count hp.1
  have hiC : i <= C := by
    have hpC : p <= PrimeFactorUnimodality.primeAt C := by exact_mod_cast hp.2.2.2
    by_contra hn
    have hmono := PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_of_not_ge hn)
    rw [hi] at hmono
    omega
  have htw : IsTwinStep i := isTwinStep_of_prime_add_two i
    (by simpa only [hi] using hpgt) (by simpa only [hi] using hp.2.1)
  have hbound : BddAbove {j | j <= C /\ IsTwinStep j} :=
    Exists.intro C (fun j hj => hj.1)
  have hne : Set.Nonempty {j | j <= C /\ IsTwinStep j} :=
    Exists.intro i (And.intro hiC htw)
  have hlast : lastTwinIndex C <= C /\ IsTwinStep (lastTwinIndex C) :=
    Nat.sSup_mem hne hbound
  have hiL : i <= lastTwinIndex C := le_csSup hbound (And.intro hiC htw)
  have hpL : p <= PrimeFactorUnimodality.primeAt (lastTwinIndex C) := by
    simpa only [hi] using PrimeFactorUnimodality.primeAt_strictMono.monotone hiL
  exact And.intro (hp.2.2.1.trans_le (by exact_mod_cast hpL))
    (PrimeFactorUnimodality.primeAt_strictMono.monotone hlast.1)

/-- Full relative location of the actual last ascents for both canonical
families. The conjectural input is solely fixed proportional twin coverage. -/
theorem both_last_ascent_relative_location_of_multiplicative_twins
    (hcoverage : MultiplicativeTwinCoverage) (eps : Real)
    (heps : 0 < eps) (heps1 : eps < 1) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k ->
      ((1 - eps) * (PrimeFactorUnimodality.primeAt (ordinaryTwinCutoffIndex k) : Real) <
          lastAscentPrime (ordinaryDensity k) /\
        lastAscentPrime (ordinaryDensity k) <=
          PrimeFactorUnimodality.primeAt (ordinaryTwinCutoffIndex k)) /\
      ((1 - eps) * (PrimeFactorUnimodality.primeAt (genericTwinCutoffIndex k) : Real) <
          lastAscentPrime (genericOddDensity k) /\
        lastAscentPrime (genericOddDensity k) <=
          PrimeFactorUnimodality.primeAt (genericTwinCutoffIndex k)) := by
  choose Ki hi using both_last_ascent_identification_of_dyadic_twins
    (dyadicTwinCoverage_of_multiplicative hcoverage)
  choose Kl hl using both_twin_cutoffs_eventually_large ((1 : Real) / 4)
    (by norm_num) (by norm_num)
  choose X hX using lastTwinIndex_eventually_relative hcoverage eps heps heps1
  choose Kx hKx using exists_nat_gt (4 * X)
  refine Exists.intro (max (max Ki Kl) Kx)
    (And.intro (hi.1.trans ((le_max_left _ _).trans (le_max_left _ _))) ?_)
  intro k hk
  have hki : Ki <= k := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
  have hkl : Kl <= k := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
  have hkx : (Kx : Real) <= k := by exact_mod_cast (le_max_right _ _).trans hk
  have hE : ((1 : Real) / 4) * k + 2 <=
      Real.exp (Real.exp (((1 : Real) / 4) * k)) := by
    linarith [Real.add_one_le_exp (((1 : Real) / 4) * k),
      Real.add_one_le_exp (Real.exp (((1 : Real) / 4) * k))]
  have hlarge := hl.2 k hkl
  have hXO : X <= (PrimeFactorUnimodality.primeAt (ordinaryTwinCutoffIndex k) : Real) := by
    linarith only [hKx, hkx, hE, hlarge.1]
  have hXG : X <= (PrimeFactorUnimodality.primeAt (genericTwinCutoffIndex k) : Real) := by
    linarith only [hKx, hkx, hE, hlarge.2]
  have hident := hi.2 k hki
  have hO : lastAscentPrime (ordinaryDensity k) =
      PrimeFactorUnimodality.primeAt (lastTwinIndex (ordinaryTwinCutoffIndex k)) :=
    congrArg PrimeFactorUnimodality.primeAt hident.1.csSup_eq
  have hG : lastAscentPrime (genericOddDensity k) =
      PrimeFactorUnimodality.primeAt (lastTwinIndex (genericTwinCutoffIndex k)) :=
    congrArg PrimeFactorUnimodality.primeAt hident.2.csSup_eq
  rw [hO, hG]
  exact And.intro (hX _ hXO) (hX _ hXG)

private theorem relative_bounds_tendsto (L X : Nat -> Real)
    (hX : forall k : Nat, 0 < X k)
    (hbound : forall eps : Real, 0 < eps -> eps < 1 ->
      exists K : Nat, forall k : Nat, K <= k ->
        (1 - eps) * X k < L k /\ L k <= X k) :
    Filter.Tendsto (fun k => L k / X k) Filter.atTop (nhds 1) := by
  apply tendsto_order.mpr
  constructor
  next =>
    intro a ha
    let eps := min ((1 - a) / 2) ((1 : Real) / 2)
    have heps : 0 < eps := lt_min (by linarith) (by norm_num)
    have heps1 : eps < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have haeps : a < 1 - eps := by
      have h := min_le_left ((1 - a) / 2) ((1 : Real) / 2)
      dsimp only [eps]
      linarith
    choose K hK using hbound eps heps heps1
    apply Filter.eventually_atTop.mpr
    refine Exists.intro K ?_
    intro k hk
    have h := div_lt_div_of_pos_right (hK k hk).1 (hX k)
    have hc : ((1 - eps) * X k) / X k = 1 - eps := by
      field_simp [ne_of_gt (hX k)]
    rw [hc] at h
    exact haeps.trans h
  next =>
    intro a ha
    choose K hK using hbound ((1 : Real) / 2) (by norm_num) (by norm_num)
    apply Filter.eventually_atTop.mpr
    refine Exists.intro K ?_
    intro k hk
    have h := div_le_div_of_nonneg_right (hK k hk).2 (hX k).le
    rw [div_self (ne_of_gt (hX k))] at h
    exact h.trans_lt ha

/-- The actual ratios L_k/X_k tend to one along the full rank sequence.
No Hardy-Littlewood or twin-coverage axiom is introduced: coverage remains
an explicit hypothesis of this conditional theorem. -/
theorem both_last_ascent_ratio_tendsto_one
    (hcoverage : MultiplicativeTwinCoverage) :
    Filter.Tendsto (fun k : Nat => (lastAscentPrime (ordinaryDensity k) : Real) /
        (PrimeFactorUnimodality.primeAt (ordinaryTwinCutoffIndex k) : Real))
      Filter.atTop (nhds 1) /\
    Filter.Tendsto (fun k : Nat => (lastAscentPrime (genericOddDensity k) : Real) /
        (PrimeFactorUnimodality.primeAt (genericTwinCutoffIndex k) : Real))
      Filter.atTop (nhds 1) := by
  have hpos : forall i : Nat, (0 : Real) < PrimeFactorUnimodality.primeAt i := by
    intro i
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt i).pos
  constructor
  next =>
    apply relative_bounds_tendsto _ _ (fun k => hpos _)
    intro eps heps heps1
    choose K hK using both_last_ascent_relative_location_of_multiplicative_twins
      hcoverage eps heps heps1
    refine Exists.intro K ?_
    intro k hk
    have h := (hK.2 k hk).1
    exact And.intro h.1 (by exact_mod_cast h.2)
  next =>
    apply relative_bounds_tendsto _ _ (fun k => hpos _)
    intro eps heps heps1
    choose K hK using both_last_ascent_relative_location_of_multiplicative_twins
      hcoverage eps heps heps1
    refine Exists.intro K ?_
    intro k hk
    have h := (hK.2 k hk).2
    exact And.intro h.1 (by exact_mod_cast h.2)

end
end PrimeFactorOscillations
