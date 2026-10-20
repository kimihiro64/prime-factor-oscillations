/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.GapRecurrence
import PrimeFactorOscillations.Assembly.LeastRecurringPrimeGap
import PrimeFactorOscillations.Assembly.PrimeProfileAttainment

/-!
# The exact optimal adaptive distortion of a prime probability profile

The least recurring gap is a universal lower distortion threshold. One
genuine same-profile law attains this threshold for every positive adaptive
probe sequence. The same constant determines the existing critical
late-ascent scale. All arithmetic inputs are unconditional.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter
open scoped Topology

namespace PrimeFactorOscillations.PrimeProfileRigidity

theorem exists_unbounded_least_gap_swap_set :
    exists A : Set Nat,
      (forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) /\
      (forall N : Nat, exists n : Nat, N <= n /\ Membership.mem A n) /\
      (forall n, Membership.mem A n ->
        PrimeFactorUnimodality.primeAt (n + 1) =
          PrimeFactorUnimodality.primeAt n + leastRecurringPrimeGap) := by
  let S : Set Nat := {n | PrimeFactorUnimodality.primeAt (n + 1) =
    PrimeFactorUnimodality.primeAt n + leastRecurringPrimeGap}
  have hS : forall N : Nat, exists n : Nat, N <= n /\ Membership.mem S n :=
    leastRecurringPrimeGap_exact_above
  have hh := Set.exists_unbounded_nonadjacent_subset S hS
  let A := Classical.choose hh
  have hd : (forall n, Membership.mem A n -> Membership.mem S n) /\
      (forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) /\
      (forall N : Nat, exists n : Nat, N <= n /\ Membership.mem A n) :=
    Classical.choose_spec hh
  exact Exists.intro A (And.intro hd.2.1 (And.intro hd.2.2 hd.1))

/-- No non-finite same-profile law beats the actual least recurring gap. -/
theorem least_gap_lower_distortion (a : Nat -> Real)
    (ha : forall n, 0 <= a n) (ha1 : forall n, a n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2))
    (heq : Complex.canonicalBernoulliProfile a =
      Complex.canonicalBernoulliProfile reciprocalPrimeProbability)
    (hfinite : Not (exists N : Nat, exists e : Equiv.Perm Nat,
      (forall n, N <= n -> e n = n) /\
        forall n, a n = reciprocalPrimeProbability (e n)))
    (t : Nat -> Real) (ht : forall n, 0 < t n) :
    forall eps : Real, 0 < eps -> forall N : Nat,
      exists n : Nat, N <= n /\ (leastRecurringPrimeGap : Real) - eps <=
        normalizedProbabilityPrefixDefect a t n :=
  profile_defect_arbitrarily_close_to_gap_floor a ha ha1 hsa heq hfinite
    leastRecurringPrimeGap leastRecurringPrimeGap_eventual_floor t ht

/-- One positive square-summable same-profile law attains the optimal gap
threshold simultaneously for every positive adaptive probe sequence. -/
theorem exists_profile_attaining_least_gap :
    exists a : Nat -> Real,
      (forall n, 0 < a n) /\
      (forall n, a n <= 1) /\
      Summable (fun n => (a n) ^ 2) /\
      (forall n, 2 * leastRecurringPrimeGap <= PrimeFactorUnimodality.primeAt n ->
        abs (a n - reciprocalPrimeProbability n) <=
          2 * (leastRecurringPrimeGap : Real) / (PrimeFactorUnimodality.primeAt n : Real) ^ 2) /\
      Complex.canonicalBernoulliProfile a =
        Complex.canonicalBernoulliProfile reciprocalPrimeProbability /\
      Not (exists N : Nat, exists e : Equiv.Perm Nat,
        (forall n, N <= n -> e n = n) /\
          forall n, a n = reciprocalPrimeProbability (e n)) /\
      (forall t : Nat -> Real, (forall n, 0 < t n) ->
        (forall n, normalizedProbabilityPrefixDefect a t n <= leastRecurringPrimeGap) /\
        (forall eps : Real, 0 < eps -> forall N : Nat, exists n : Nat,
          N <= n /\ (leastRecurringPrimeGap : Real) - eps <=
            normalizedProbabilityPrefixDefect a t n)) := by
  let A := Classical.choose exists_unbounded_least_gap_swap_set
  have hd : (forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) /\
      (forall N : Nat, exists n : Nat, N <= n /\ Membership.mem A n) /\
      (forall n, Membership.mem A n -> PrimeFactorUnimodality.primeAt (n + 1) =
        PrimeFactorUnimodality.primeAt n + leastRecurringPrimeGap) :=
    Classical.choose_spec exists_unbounded_least_gap_swap_set
  let a := adjacentSwapProfileLaw A hd.1
  refine Exists.intro a ?_
  refine And.intro (adjacentSwapProfileLaw_pos A hd.1) ?_
  refine And.intro (adjacentSwapProfileLaw_le_one A hd.1) ?_
  refine And.intro (summable_adjacentSwapProfileLaw_sq A hd.1) ?_
  refine And.intro (fun n hn => adjacentSwapProfileLaw_probability_error
    A hd.1 leastRecurringPrimeGap hd.2.2 n hn) ?_
  refine And.intro (canonicalProfile_adjacentSwapProfileLaw A hd.1) ?_
  refine And.intro (adjacentSwapProfileLaw_not_finite A hd.1 hd.2.1) ?_
  intro t ht
  exact And.intro
    (adjacentSwapProfileLaw_cost_le A hd.1 leastRecurringPrimeGap hd.2.2 t ht)
    (adjacentSwapProfileLaw_cost_arbitrarily_close A hd.1 hd.2.1
      leastRecurringPrimeGap hd.2.2 t ht)

/-- The same rigorously defined optimal cost governs the maintained
prime-density late-ascent threshold in both canonical laws. -/
theorem least_gap_late_ascent_critical_scale :
    (forall b : Real, 0 < b -> b < 1 / ((leastRecurringPrimeGap : Real) + 1) ->
      forall K Q : Nat, exists k i : Nat, K <= k /\
        Q <= PrimeFactorUnimodality.primeAt i /\
        b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) /\
        genericOddDensity k i < genericOddDensity k (i + 1) /\
        ordinaryDensity k i < ordinaryDensity k (i + 1)) /\
    (forall b : Real, 1 / ((leastRecurringPrimeGap : Real) + 1) < b ->
      exists K Q : Nat, forall k i : Nat, K <= k ->
        Q <= PrimeFactorUnimodality.primeAt i ->
        b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) ->
        genericOddDensity k (i + 1) < genericOddDensity k i /\
        ordinaryDensity k (i + 1) < ordinaryDensity k i) :=
  late_ascent_critical_scale leastRecurringPrimeGap
    (by have h := two_le_leastRecurringPrimeGap; omega)
    leastRecurringPrimeGap_recurrent leastRecurringPrimeGap_eventual_floor

/-- Cost two is exactly recurrence of prime gaps at most two. -/
theorem least_gap_eq_two_iff :
    leastRecurringPrimeGap = 2 <-> RecurrentPrimeGapAtMost 2 := by
  classical
  constructor
  . intro h
    simpa only [h] using leastRecurringPrimeGap_recurrent
  . intro h
    have hle : leastRecurringPrimeGap <= 2 :=
      Nat.find_min' (Exists.intro 600 recurrentPrimeGapAtMost_600) h
    exact le_antisymm hle two_le_leastRecurringPrimeGap

end PrimeFactorOscillations.PrimeProfileRigidity
