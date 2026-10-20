/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.PrimeProfileZeroHoles
import PrimeFactorOscillations.Helpers.PrimeProfileUniformDichotomy

/-!
# Complete probe-uniform distortion alternatives for the prime profile

Every admissible law with the reciprocal-prime entire profile has either
one finite even distortion envelope, shared by all positive probes, or
arbitrarily late lower witnesses shared by all positive probes.
A zero coordinate gives the stronger eventual uniform divergence.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- A zero coordinate forces eventual divergence uniformly in the probe. -/
theorem zero_hole_forces_eventually_uniform_divergence (a : Nat -> Real)
    (ha : forall n, 0 <= a n) (ha1 : forall n, a n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2))
    (heq : Complex.canonicalBernoulliProfile a =
      Complex.canonicalBernoulliProfile reciprocalPrimeProbability)
    (hzero : exists i : Nat, a i = 0) :
    forall C : Real, exists M : Nat, forall n : Nat, M <= n ->
      forall v : Nat -> Real, 0 < v n ->
        C < normalizedProbabilityPrefixDefect a v n := by
  intro C
  let i := Classical.choose hzero
  have hi : a i = 0 := Classical.choose_spec hzero
  have hP : exists P : Nat, 4 * C < (P : Real) := exists_nat_gt _
  let P := Classical.choose hP
  have hPgt : 4 * C < (P : Real) := Classical.choose_spec hP
  refine Exists.intro (max i P) ?_
  intro n hn v hv
  have hin : i <= n := (le_max_left i P).trans hn
  have hPn : P <= n := (le_max_right i P).trans hn
  have hpr : (P : Real) <= (PrimeFactorUnimodality.primeAt n : Real) := by
    exact_mod_cast hPn.trans (PrimeFactorUnimodality.primeAt_strictMono.id_le n)
  have hl := quarter_prime_le_normalized_defect_of_zero a ha ha1 hsa heq v i n hi hin hv
  linarith only [hPgt, hpr, hl]

/-- The finite even and uniform unbounded alternatives cover every admissible
law having the reciprocal-prime entire probability profile. -/
theorem same_profile_uniform_distortion_dichotomy (a : Nat -> Real)
    (ha : forall n, 0 <= a n) (ha1 : forall n, a n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2))
    (heq : Complex.canonicalBernoulliProfile a =
      Complex.canonicalBernoulliProfile reciprocalPrimeProbability) :
    (exists K : Nat,
      (forall eps : Real, 0 < eps -> exists M : Nat,
        forall n : Nat, M <= n -> forall v : Nat -> Real, 0 < v n ->
          normalizedProbabilityPrefixDefect a v n <= 2 * (K : Real) + eps) /\
      (forall eps : Real, 0 < eps -> forall N : Nat,
        exists n : Nat, N <= n /\
          forall v : Nat -> Real, 0 < v n ->
            2 * (K : Real) - eps <= normalizedProbabilityPrefixDefect a v n)) \/
    (forall C : Real, forall N : Nat, exists n : Nat, N <= n /\
      forall v : Nat -> Real, 0 < v n ->
        C < normalizedProbabilityPrefixDefect a v n) := by
  classical
  by_cases hpos : forall n, 0 < a n
  . have hex := exists_prime_perm_of_positive_profile_eq a hpos ha1 hsa heq
    let e := Classical.choose hex
    have he : forall n, a n = reciprocalPrimeProbability (e n) := Classical.choose_spec hex
    have hd := prime_profile_uniform_distortion_dichotomy e
    cases hd with
    | inl hfinite =>
      let K := Classical.choose hfinite
      have hK := Classical.choose_spec hfinite
      apply Or.inl
      refine Exists.intro K (And.intro ?_ ?_)
      . intro eps heps
        let M := Classical.choose (hK.1 eps heps)
        have hM := Classical.choose_spec (hK.1 eps heps)
        refine Exists.intro M ?_
        intro n hn v hv
        rw [normalizedProbabilityPrefixDefect_eq_of_prime_perm a e he v n]
        exact hM n hn v hv
      . intro eps heps N
        let n := Classical.choose (hK.2 eps heps N)
        have hn := Classical.choose_spec (hK.2 eps heps N)
        refine Exists.intro n (And.intro hn.1 ?_)
        intro v hv
        rw [normalizedProbabilityPrefixDefect_eq_of_prime_perm a e he v n]
        exact hn.2 v hv
    | inr hinfty =>
      apply Or.inr
      intro C N
      let n := Classical.choose (hinfty C N)
      have hn := Classical.choose_spec (hinfty C N)
      refine Exists.intro n (And.intro hn.1 ?_)
      intro v hv
      rw [normalizedProbabilityPrefixDefect_eq_of_prime_perm a e he v n]
      exact hn.2 v hv
  . have hsome : exists i : Nat, Not (0 < a i) := by
      by_contra h
      apply hpos
      intro i
      by_contra hi
      exact h (Exists.intro i hi)
    let i := Classical.choose hsome
    have hi : Not (0 < a i) := Classical.choose_spec hsome
    have hz : a i = 0 := le_antisymm (le_of_not_gt hi) (ha i)
    have hevent := zero_hole_forces_eventually_uniform_divergence
      a ha ha1 hsa heq (Exists.intro i hz)
    apply Or.inr
    intro C N
    let M := Classical.choose (hevent C)
    have hM := Classical.choose_spec (hevent C)
    refine Exists.intro (max N M) (And.intro (le_max_left N M) ?_)
    intro v hv
    exact hM (max N M) (le_max_right N M) v hv

end PrimeFactorOscillations.PrimeProfileRigidity
