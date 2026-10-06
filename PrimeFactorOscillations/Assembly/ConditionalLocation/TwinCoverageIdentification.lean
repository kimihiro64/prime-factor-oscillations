/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.TwinPotentialWindows

/-!
# Twin Coverage Identification

Maintained implementation of the conditional last-ascent location argument.
The arithmetic coverage assumptions remain explicit; no conjecture is an axiom.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- A lower twin member in every sufficiently large dyadic interval. -/
def DyadicTwinCoverage : Prop :=
  exists N : Nat, forall n : Nat, N <= n ->
    exists p : Nat, Nat.Prime p /\ Nat.Prime (p + 2) /\ n < p /\ p <= 2 * n

/-- Fixed proportional intervals only; no shrinking-epsilon uniformity. -/
def MultiplicativeTwinCoverage : Prop :=
  forall eps : Real, 0 < eps -> eps < 1 -> exists X : Real,
    forall x : Real, X <= x -> exists p : Nat,
      Nat.Prime p /\ Nat.Prime (p + 2) /\ (1 - eps) * x < p /\ (p : Real) <= x

theorem dyadicTwinCoverage_of_multiplicative
    (hcoverage : MultiplicativeTwinCoverage) : DyadicTwinCoverage := by
  choose X hX using hcoverage ((1 : Real) / 2) (by norm_num) (by norm_num)
  choose N hN using exists_nat_gt (max X (1 : Real))
  refine Exists.intro N ?_
  intro n hn
  have hNn : (N : Real) <= n := by exact_mod_cast hn
  have hx : X <= 2 * (n : Real) := by
    have h1 := (le_max_left X (1 : Real)).trans_lt hN
    have h2 := (le_max_right X (1 : Real)).trans_lt hN
    linarith
  choose p hp using hX (2 * n) hx
  refine Exists.intro p (And.intro hp.1 (And.intro hp.2.1 (And.intro ?_ ?_)))
  next =>
    have h : (n : Real) < p := by linarith only [hp.2.2.1]
    exact_mod_cast h
  next => exact_mod_cast hp.2.2.2

/-- Exact last-ascent identification from dyadic twin coverage alone.
Every density, rank, support condition and cutoff in the conclusion is concrete. -/
theorem both_last_ascent_identification_of_dyadic_twins
    (hcoverage : DyadicTwinCoverage) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k ->
      IsGreatest {i | ordinaryDensity k i < ordinaryDensity k (i + 1)}
        (lastTwinIndex (ordinaryTwinCutoffIndex k)) /\
      IsGreatest {i | genericOddDensity k i < genericOddDensity k (i + 1)}
        (lastTwinIndex (genericTwinCutoffIndex k)) := by
  choose N0 hN0 using hcoverage
  choose Kt Q ht using both_last_ascents_are_last_twins_of_late_anchor
    ((2 : Real) / 9) (by norm_num)
  choose Kw hw using both_twin_potential_on_window ((1 : Real) / 4)
    (by norm_num) (by norm_num)
  choose K0 hK0 using exists_nat_gt
    (max (36 * Real.log 2) (4 * max (N0 : Real) (Q : Real)))
  refine Exists.intro (max (max Kt Kw) K0)
    (And.intro (ht.1.trans ((le_max_left _ _).trans (le_max_left _ _))) ?_)
  intro k hk
  have hkt : Kt <= k := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
  have hkw : Kw <= k := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
  have hk0 : (K0 : Real) <= k := by exact_mod_cast (le_max_right _ _).trans hk
  have hlogbudget : 36 * Real.log 2 < (k : Real) :=
    ((le_max_left _ _).trans_lt hK0).trans_le hk0
  have hfixed : 4 * max (N0 : Real) (Q : Real) < (k : Real) :=
    ((le_max_right _ _).trans_lt hK0).trans_le hk0
  let N := Nat.ceil (Real.exp (Real.exp (((1 : Real) / 4) * k)))
  have hE : ((1 : Real) / 4) * k + 2 <=
      Real.exp (Real.exp (((1 : Real) / 4) * k)) := by
    linarith [Real.add_one_le_exp (((1 : Real) / 4) * k),
      Real.add_one_le_exp (Real.exp (((1 : Real) / 4) * k))]
  have hceil : Real.exp (Real.exp (((1 : Real) / 4) * k)) <= (N : Real) :=
    Nat.le_ceil _
  have hN0le : N0 <= N := by
    have h := le_max_left (N0 : Real) (Q : Real)
    have hreal : (N0 : Real) <= N := by linarith
    exact_mod_cast hreal
  have hQle : Q <= N := by
    have h := le_max_right (N0 : Real) (Q : Real)
    have hreal : (Q : Real) <= N := by linarith
    exact_mod_cast hreal
  choose p hp using hN0 N hN0le
  let i := Nat.count Nat.Prime p
  have hi : PrimeFactorUnimodality.primeAt i = p := Nat.nth_count hp.1
  have hlo : N <= PrimeFactorUnimodality.primeAt i := by
    simpa only [hi] using hp.2.2.1.le
  have hhi : PrimeFactorUnimodality.primeAt i <= 4 * N := by
    rw [hi]
    omega
  have hwindow := hw.2 k hkw
  have hpot := hwindow.2 i hlo hhi
  have hband := Real.ceil_double_exp_prime_prefix_additive_band hwindow.1 hlo hhi
  have hscale : ((2 : Real) / 9) * k <=
      Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) := by
    linarith only [hband.1, hlogbudget]
  have htw : IsTwinStep i := isTwinStep_of_prime_add_two i hpot.1.1
    (by simpa only [hi] using hp.2.1)
  exact ht.2.2 k hkt i (hQle.trans hlo) hscale htw hpot.1 hpot.2

end PrimeFactorOscillations
