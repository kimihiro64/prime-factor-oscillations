/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.PrimeProfileCutoffInverse
import PrimeFactorOscillations.Helpers.PrimeProfileTwoStepTransport

/-!
# A probability-profile equivalence for recurrent short prime quadruplets

One coordinate permutation is chosen before every positive probe sequence.
Its full signed cutoff cost has sharp upper limit twelve and recurrent
double crossings. The converse uses the strict fourteen inverse threshold.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter
open scoped Topology

namespace PrimeFactorOscillations.PrimeProfileRigidity

def primePermutationProfileLaw (e : Equiv.Perm Nat) (n : Nat) : Real :=
  reciprocalPrimeProbability (e n)

theorem primePermutationProfileLaw_properties (e : Equiv.Perm Nat) :
    (forall n, 0 < primePermutationProfileLaw e n) /\
    (forall n, primePermutationProfileLaw e n <= 1) /\
    Summable (fun n => (primePermutationProfileLaw e n) ^ 2) /\
    Complex.canonicalBernoulliProfile (primePermutationProfileLaw e) =
      Complex.canonicalBernoulliProfile reciprocalPrimeProbability := by
  refine And.intro (fun n => reciprocalPrimeProbability_pos (e n))
    (And.intro (fun n => reciprocalPrimeProbability_le_one (e n)) (And.intro ?_ ?_))
  . have hs := summable_reciprocalPrimeProbability_sq.comp_injective (i := e) e.injective
    apply hs.congr
    intro n
    rfl
  . funext z
    exact Complex.canonicalBernoulliProfile_comp_equiv reciprocalPrimeProbability e z

theorem normalized_primePermutationProfileLaw (e : Equiv.Perm Nat)
    (t : Nat -> Real) (n : Nat) :
    normalizedProbabilityPrefixDefect (primePermutationProfileLaw e) t n =
      normalizedPrimePrefixDefect e t n := by
  unfold normalizedProbabilityPrefixDefect normalizedPrimePrefixDefect Finset.prefixDefect
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  simp only [primePermutationProfileLaw, primeLogWeight, reciprocalPrimeProbability,
    Real.bernoulliLogProfile, mul_one_div]

theorem primePermutationProfileLaw_cost_arbitrarily_close_to_twelve
    (e : Equiv.Perm Nat) (t : Nat -> Real) (ht : forall n, 0 < t n)
    (hcross : forall N : Nat, exists k : Nat,
      N <= k /\ 2 <= Finset.prefixDisplacement e (k + 2)) :
    forall eps : Real, 0 < eps -> forall N : Nat,
      exists k : Nat, N <= k /\
        12 - eps <= normalizedProbabilityPrefixDefect
          (primePermutationProfileLaw e) t (k + 1) := by
  simpa only [normalized_primePermutationProfileLaw] using
    two_crossing_defect_arbitrarily_close_to_twelve e t ht hcross

/-- Recurring double crossings exclude every finite permutation representation. -/
theorem primePermutationProfileLaw_not_finite
    (e : Equiv.Perm Nat)
    (hcross : forall N : Nat, exists k : Nat,
      N <= k /\ 2 <= Finset.prefixDisplacement e (k + 2)) :
    Not (exists N : Nat, exists f : Equiv.Perm Nat,
      (forall n, N <= n -> f n = n) /\
        forall n, primePermutationProfileLaw e n = reciprocalPrimeProbability (f n)) := by
  intro hh
  have hp := primePermutationProfileLaw_properties e
  let t : Nat -> Real := fun _ => 1
  have ht : forall n, 0 < t n := fun _ => by norm_num [t]
  have hz := (positive_profile_cutoff_inverse (primePermutationProfileLaw e)
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 t ht).mpr hh
  have hevent := eventually_atTop.mp
    (hz.eventually (gt_mem_nhds (by norm_num : (0 : Real) < 1)))
  let M := Classical.choose hevent
  have hM : forall n : Nat, M <= n ->
      normalizedProbabilityPrefixDefect (primePermutationProfileLaw e) t n < 1 :=
    Classical.choose_spec hevent
  have hlow := primePermutationProfileLaw_cost_arbitrarily_close_to_twelve
    e t ht hcross 1 (by norm_num) M
  let k := Classical.choose hlow
  have hk : M <= k /\
      12 - 1 <= normalizedProbabilityPrefixDefect (primePermutationProfileLaw e) t (k + 1) :=
    Classical.choose_spec hlow
  have hs := hM (k + 1) (by omega)
  linarith only [hk.2, hs]

/-- A single law, selected before all probes, realizes the sharp twelve threshold. -/
theorem recurrent_quadruplet_iff_probe_uniform_twelve_profile :
    (forall N : Nat, exists k : Nat, N <= k /\ IsShortPrimeQuadruplet k) <->
    exists e : Equiv.Perm Nat,
      (forall N : Nat, exists k : Nat,
        N <= k /\ 2 <= Finset.prefixDisplacement e (k + 2)) /\
      (forall eps : Real, 0 < eps -> exists N : Nat,
        forall k : Nat, N <= k -> forall t : Nat -> Real,
          0 < t (k + 1) ->
          normalizedProbabilityPrefixDefect (primePermutationProfileLaw e) t (k + 1)
            <= 12 + eps) := by
  constructor
  . intro hrec
    have hs := exists_unbounded_quadruplet_twoStepSupport hrec
    let B := Classical.choose hs
    have hB :
        (forall n, Membership.mem B n -> Not (Membership.mem B (n + 2))) /\
        (forall n, Membership.mem B n ->
          PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6) /\
        (forall N : Nat, exists k : Nat, N <= k /\
          Membership.mem B k /\ Membership.mem B (k + 1)) :=
      Classical.choose_spec hs
    let e := Finset.twoStepSwapPerm B hB.1
    refine Exists.intro e (And.intro ?_ ?_)
    . intro N
      let k := Classical.choose (hB.2.2 N)
      have hk : N <= k /\ Membership.mem B k /\ Membership.mem B (k + 1) :=
        Classical.choose_spec (hB.2.2 N)
      exact Exists.intro k (And.intro hk.1
        (Finset.two_le_prefixDisplacement_twoStepSwapPerm B hB.1 k hk.2.1 hk.2.2))
    . intro eps heps
      have hu := eventual_uniform_twoStepSwap_cost_le B hB.1 hB.2.1 eps heps
      let N := Classical.choose hu
      have hN : forall k : Nat, N <= k -> forall t : Nat -> Real,
          0 < t (k + 1) ->
          normalizedPrimePrefixDefect e t (k + 1) <= 12 + eps :=
        Classical.choose_spec hu
      refine Exists.intro N ?_
      intro k hk t ht
      rw [normalized_primePermutationProfileLaw]
      exact hN k hk t ht
  . intro hex
    let e := Classical.choose hex
    have he :
        (forall N : Nat, exists k : Nat,
          N <= k /\ 2 <= Finset.prefixDisplacement e (k + 2)) /\
        (forall eps : Real, 0 < eps -> exists N : Nat,
          forall k : Nat, N <= k -> forall t : Nat -> Real,
            0 < t (k + 1) ->
            normalizedProbabilityPrefixDefect (primePermutationProfileLaw e) t (k + 1)
              <= 12 + eps) :=
      Classical.choose_spec hex
    let t : Nat -> Real := fun _ => 1
    have ht : forall n, 0 < t n := fun _ => by norm_num [t]
    have hu := he.2 1 (by norm_num)
    let N := Classical.choose hu
    have hN : forall k : Nat, N <= k -> forall t : Nat -> Real,
        0 < t (k + 1) ->
        normalizedProbabilityPrefixDefect (primePermutationProfileLaw e) t (k + 1) <= 12 + 1 :=
      Classical.choose_spec hu
    have hupper : Filter.Eventually (fun k : Nat =>
        normalizedPrimePrefixDefect e t (k + 1) <= 12 + 1) atTop := by
      apply eventually_atTop.mpr
      refine Exists.intro N ?_
      intro k hk
      have hb := hN k hk t (ht (k + 1))
      rw [normalized_primePermutationProfileLaw] at hb
      exact hb
    exact recurrent_quadruplet_of_infinite_double_crossings e t ht
      (12 + 1) (by norm_num) hupper he.1

end PrimeFactorOscillations.PrimeProfileRigidity
