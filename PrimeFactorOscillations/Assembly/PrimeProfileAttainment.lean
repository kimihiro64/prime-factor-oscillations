/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.PrimeProfileDistortion
import PrimeFactorOscillations.Mathlib.Combinatorics.AdjacentSwapPrefix

/-!
# Exact adaptive distortion of adjacent prime-coordinate swaps

The construction is a genuine positive square-summable same-profile law.
The entire cutoff defect is its single crossing pair. A constant recurring
gap bounds every defect above and is approached at arbitrarily large cutoffs.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

attribute [local instance] Classical.propDecidable

open Filter
open scoped Topology

namespace PrimeFactorOscillations.PrimeProfileRigidity

def adjacentSwapProfileLaw (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1)))
    (n : Nat) : Real :=
  reciprocalPrimeProbability ((Finset.adjacentSwapPerm A hA) n)

theorem adjacentSwapProfileLaw_pos (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) (n : Nat) :
    0 < adjacentSwapProfileLaw A hA n :=
  reciprocalPrimeProbability_pos _

theorem adjacentSwapProfileLaw_le_one (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) (n : Nat) :
    adjacentSwapProfileLaw A hA n <= 1 :=
  reciprocalPrimeProbability_le_one _

theorem summable_adjacentSwapProfileLaw_sq (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) :
    Summable (fun n => (adjacentSwapProfileLaw A hA n) ^ 2) := by
  have hs := summable_reciprocalPrimeProbability_sq.comp_injective
    (i := Finset.adjacentSwapPerm A hA) (Finset.adjacentSwapPerm A hA).injective
  apply hs.congr
  intro n
  rfl

theorem canonicalProfile_adjacentSwapProfileLaw (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) :
    Complex.canonicalBernoulliProfile (adjacentSwapProfileLaw A hA) =
      Complex.canonicalBernoulliProfile reciprocalPrimeProbability := by
  funext z
  exact Complex.canonicalBernoulliProfile_comp_equiv reciprocalPrimeProbability
    (Finset.adjacentSwapPerm A hA) z

/-- The whole compensated defect consists of exactly the crossing pair. -/
theorem normalized_adjacentSwapProfileLaw (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1)))
    (t : Nat -> Real) (n : Nat) :
    normalizedProbabilityPrefixDefect (adjacentSwapProfileLaw A hA) t n =
      if Membership.mem A n then
        (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
          ((PrimeFactorUnimodality.primeAt n : Real) + t n) / (t n) ^ 2 *
            Real.pairLogDefect (t n) (PrimeFactorUnimodality.primeAt n : Real)
              (PrimeFactorUnimodality.primeAt (n + 1) : Real)
      else 0 := by
  have hid : normalizedProbabilityPrefixDefect (adjacentSwapProfileLaw A hA) t n =
      normalizedPrimePrefixDefect (Finset.adjacentSwapPerm A hA) t n := by
    unfold normalizedProbabilityPrefixDefect normalizedPrimePrefixDefect Finset.prefixDefect
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    simp only [adjacentSwapProfileLaw, primeLogWeight, reciprocalPrimeProbability,
      Real.bernoulliLogProfile, mul_one_div]
  rw [hid]
  unfold normalizedPrimePrefixDefect
  rw [Finset.prefixDefect_adjacentSwapPerm]
  by_cases hn : Membership.mem A n
  . simp only [ite_eq_left hn, Real.pairLogDefect, primeLogWeight]
  . simp only [ite_eq_right hn, mul_zero]

/-- Both sharp scalar bounds survive in the actual probability observable. -/
theorem adjacentSwapProfileLaw_cost_bounds (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1)))
    (t : Nat -> Real) (n : Nat) (ht : 0 < t n) (hn : Membership.mem A n) :
    ((PrimeFactorUnimodality.primeAt (n + 1) : Real) -
        (PrimeFactorUnimodality.primeAt n : Real)) *
      ((PrimeFactorUnimodality.primeAt n : Real) /
        (PrimeFactorUnimodality.primeAt (n + 1) : Real)) ^ 2 <=
      normalizedProbabilityPrefixDefect (adjacentSwapProfileLaw A hA) t n /\
    normalizedProbabilityPrefixDefect (adjacentSwapProfileLaw A hA) t n <=
      ((PrimeFactorUnimodality.primeAt (n + 1) : Real) -
        (PrimeFactorUnimodality.primeAt n : Real)) *
      ((PrimeFactorUnimodality.primeAt n : Real) /
        (PrimeFactorUnimodality.primeAt (n + 1) : Real)) := by
  rw [normalized_adjacentSwapProfileLaw, ite_eq_left hn]
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hq : (0 : Real) < PrimeFactorUnimodality.primeAt (n + 1) := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (n + 1)).pos
  have hpq : (PrimeFactorUnimodality.primeAt n : Real) <=
      (PrimeFactorUnimodality.primeAt (n + 1) : Real) := by
    exact_mod_cast (PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self n)).le
  exact And.intro
    (Real.gap_mul_ratio_sq_le_normalized_pairLogDefect (t n) _ _ ht hp hpq)
    (Real.normalized_pairLogDefect_le_gap_mul_ratio (t n) _ _ ht hp hq)

theorem adjacentSwapProfileLaw_not_finite (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1)))
    (hunbounded : forall N : Nat, exists n : Nat, N <= n /\ Membership.mem A n) :
    Not (exists N : Nat, exists e : Equiv.Perm Nat,
      (forall n, N <= n -> e n = n) /\
        forall n, adjacentSwapProfileLaw A hA n = reciprocalPrimeProbability (e n)) := by
  intro hh
  let N := Classical.choose hh
  let e := Classical.choose (Classical.choose_spec hh)
  have he : (forall n, N <= n -> e n = n) /\
      forall n, adjacentSwapProfileLaw A hA n = reciprocalPrimeProbability (e n) :=
    Classical.choose_spec (Classical.choose_spec hh)
  let n := Classical.choose (hunbounded N)
  have hn : N <= n /\ Membership.mem A n := Classical.choose_spec (hunbounded N)
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hpq : (PrimeFactorUnimodality.primeAt n : Real) <
      (PrimeFactorUnimodality.primeAt (n + 1) : Real) := by
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self n)
  have hstrict : reciprocalPrimeProbability (n + 1) < reciprocalPrimeProbability n :=
    one_div_lt_one_div_of_lt hp hpq
  have hvalue : adjacentSwapProfileLaw A hA n = reciprocalPrimeProbability (n + 1) := by
    change reciprocalPrimeProbability (Finset.adjacentSwapPartner A n) = _
    simp only [Finset.adjacentSwapPartner, ite_eq_left hn.2]
  have heq := he.2 n
  rw [he.1 n hn.1, hvalue] at heq
  exact (ne_of_lt hstrict) heq

/-- A constant gap on the chosen pairs bounds every positive-probe defect. -/
theorem adjacentSwapProfileLaw_cost_le (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1)))
    (h : Nat)
    (hgap : forall n, Membership.mem A n ->
      PrimeFactorUnimodality.primeAt (n + 1) = PrimeFactorUnimodality.primeAt n + h)
    (t : Nat -> Real) (ht : forall n, 0 < t n) (n : Nat) :
    normalizedProbabilityPrefixDefect (adjacentSwapProfileLaw A hA) t n <= h := by
  by_cases hn : Membership.mem A n
  . have hb := (adjacentSwapProfileLaw_cost_bounds A hA t n (ht n) hn).2
    have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
      exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
    have hpq : (PrimeFactorUnimodality.primeAt n : Real) <=
        (PrimeFactorUnimodality.primeAt (n + 1) : Real) := by
      exact_mod_cast (PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self n)).le
    have hr : (PrimeFactorUnimodality.primeAt n : Real) /
        (PrimeFactorUnimodality.primeAt (n + 1) : Real) <= 1 := by
      simpa only [div_self hp.ne'] using
        div_le_div_of_nonneg_left hp.le hp hpq
    have hg : (PrimeFactorUnimodality.primeAt (n + 1) : Real) -
        (PrimeFactorUnimodality.primeAt n : Real) = (h : Real) := by
      have hc : (PrimeFactorUnimodality.primeAt (n + 1) : Real) =
          (PrimeFactorUnimodality.primeAt n : Real) + (h : Real) := by
        exact_mod_cast hgap n hn
      linarith only [hc]
    rw [hg] at hb
    exact hb.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hr
        (by positivity : (0 : Real) <= h))
  . rw [normalized_adjacentSwapProfileLaw, ite_eq_right hn]
    positivity

/-- The same law approaches the gap constant for every adaptive probe sequence. -/
theorem adjacentSwapProfileLaw_cost_arbitrarily_close (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1)))
    (hunbounded : forall N : Nat, exists n : Nat, N <= n /\ Membership.mem A n)
    (h : Nat)
    (hgap : forall n, Membership.mem A n ->
      PrimeFactorUnimodality.primeAt (n + 1) = PrimeFactorUnimodality.primeAt n + h)
    (t : Nat -> Real) (ht : forall n, 0 < t n) :
    forall eps : Real, 0 < eps -> forall N : Nat, exists n : Nat,
      N <= n /\ (h : Real) - eps <=
        normalizedProbabilityPrefixDefect (adjacentSwapProfileLaw A hA) t n := by
  intro eps heps N
  have hr : Tendsto (fun n : Nat =>
      (PrimeFactorUnimodality.primeAt n : Real) /
        (PrimeFactorUnimodality.primeAt (n + 1) : Real)) atTop (nhds 1) := by
    simpa only [Nat.add_zero] using tendsto_primeAt_shift_div_shift 1 0
  have hl : Tendsto (fun n : Nat => (h : Real) *
      ((PrimeFactorUnimodality.primeAt n : Real) /
        (PrimeFactorUnimodality.primeAt (n + 1) : Real)) ^ 2) atTop (nhds (h : Real)) := by
    simpa only [one_pow, mul_one] using tendsto_const_nhds.mul (hr.pow 2)
  have hnear := hl.eventually (lt_mem_nhds (sub_lt_self (h : Real) heps))
  let M := Classical.choose (eventually_atTop.mp hnear)
  have hM : forall n : Nat, M <= n -> (h : Real) - eps < (h : Real) *
      ((PrimeFactorUnimodality.primeAt n : Real) /
        (PrimeFactorUnimodality.primeAt (n + 1) : Real)) ^ 2 :=
    Classical.choose_spec (eventually_atTop.mp hnear)
  let n := Classical.choose (hunbounded (max N M))
  have hn : max N M <= n /\ Membership.mem A n :=
    Classical.choose_spec (hunbounded (max N M))
  have hb := (adjacentSwapProfileLaw_cost_bounds A hA t n (ht n) hn.2).1
  have hg : (PrimeFactorUnimodality.primeAt (n + 1) : Real) -
      (PrimeFactorUnimodality.primeAt n : Real) = (h : Real) := by
    have hc : (PrimeFactorUnimodality.primeAt (n + 1) : Real) =
        (PrimeFactorUnimodality.primeAt n : Real) + (h : Real) := by
      exact_mod_cast hgap n hn.2
    linarith only [hc]
  rw [hg] at hb
  exact Exists.intro n (And.intro ((le_max_left N M).trans hn.1)
    ((hM n ((le_max_right N M).trans hn.1)).le.trans hb))

/-- The constructed law remains in the reciprocal-prime local-law class,
with explicit constant and all exceptional small denominators retained. -/
theorem adjacentSwapProfileLaw_probability_error (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1)))
    (h : Nat)
    (hgap : forall n, Membership.mem A n ->
      PrimeFactorUnimodality.primeAt (n + 1) = PrimeFactorUnimodality.primeAt n + h)
    (n : Nat) (hcut : 2 * h <= PrimeFactorUnimodality.primeAt n) :
    abs (adjacentSwapProfileLaw A hA n - reciprocalPrimeProbability n) <=
      2 * (h : Real) / (PrimeFactorUnimodality.primeAt n : Real) ^ 2 := by
  have hdist : abs ((PrimeFactorUnimodality.primeAt n : Real) -
      (PrimeFactorUnimodality.primeAt ((Finset.adjacentSwapPerm A hA) n) : Real)) <= h := by
    change abs ((PrimeFactorUnimodality.primeAt n : Real) -
      (PrimeFactorUnimodality.primeAt (Finset.adjacentSwapPartner A n) : Real)) <= h
    by_cases hn : Membership.mem A n
    . simp only [Finset.adjacentSwapPartner, ite_eq_left hn]
      have hc : (PrimeFactorUnimodality.primeAt (n + 1) : Real) =
          (PrimeFactorUnimodality.primeAt n : Real) + (h : Real) := by
        exact_mod_cast hgap n hn
      have hd : (PrimeFactorUnimodality.primeAt n : Real) -
          (PrimeFactorUnimodality.primeAt (n + 1) : Real) = -(h : Real) := by
        linarith only [hc]
      rw [hd, abs_neg, abs_of_nonneg (by positivity : (0 : Real) <= h)]
    . by_cases hpos : 0 < n
      . by_cases hprev : Membership.mem A (n - 1)
        . simp only [Finset.adjacentSwapPartner, ite_eq_right hn, ite_eq_left hpos,
            ite_eq_left hprev]
          have he : n - 1 + 1 = n := by omega
          have hg := hgap (n - 1) hprev
          rw [he] at hg
          have hc : (PrimeFactorUnimodality.primeAt n : Real) =
              (PrimeFactorUnimodality.primeAt (n - 1) : Real) + (h : Real) := by
            exact_mod_cast hg
          have hd : (PrimeFactorUnimodality.primeAt n : Real) -
              (PrimeFactorUnimodality.primeAt (n - 1) : Real) = (h : Real) := by
            linarith only [hc]
          rw [hd, abs_of_nonneg (by positivity : (0 : Real) <= h)]
        . simp only [Finset.adjacentSwapPartner, ite_eq_right hn, ite_eq_left hpos,
            ite_eq_right hprev, sub_self, abs_zero]
          positivity
      . simp only [Finset.adjacentSwapPartner, ite_eq_right hn, ite_eq_right hpos,
          sub_self, abs_zero]
        positivity
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hq : (0 : Real) < PrimeFactorUnimodality.primeAt ((Finset.adjacentSwapPerm A hA) n) := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt _).pos
  have hcutR : 2 * (h : Real) <= PrimeFactorUnimodality.primeAt n := by exact_mod_cast hcut
  exact Real.abs_reciprocal_difference_le_twice_gap _ _ (h : Real) hp hq hdist hcutR

end PrimeFactorOscillations.PrimeProfileRigidity
