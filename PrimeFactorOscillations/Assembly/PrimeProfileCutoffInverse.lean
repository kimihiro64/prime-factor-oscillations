/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileCutoffRigidity
import PrimeFactorOscillations.Helpers.PrimeReciprocalSquareTail
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.BernoulliProfileReconstruction

/-!
# Inverse cutoff criterion inside the reciprocal-prime profile class

The previously proved entire-profile inverse identifies the coordinate
permutation. The signed cutoff estimate then determines exactly when this
permutation is finite, without a reciprocal-intercept hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter
open scoped Topology

namespace PrimeFactorOscillations.PrimeProfileRigidity

def reciprocalPrimeProbability (n : Nat) : Real :=
  1 / (PrimeFactorUnimodality.primeAt n : Real)

theorem reciprocalPrimeProbability_pos (n : Nat) :
    0 < reciprocalPrimeProbability n := by
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  exact one_div_pos.mpr hp

theorem reciprocalPrimeProbability_le_one (n : Nat) :
    reciprocalPrimeProbability n <= 1 := by
  have hp : (1 : Real) <= PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).one_le
  simpa only [reciprocalPrimeProbability, div_one] using
    one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hp

theorem summable_reciprocalPrimeProbability_sq :
    Summable (fun n : Nat => (reciprocalPrimeProbability n) ^ 2) := by
  let f : Nat -> Nat.Primes := fun n =>
    Subtype.mk (PrimeFactorUnimodality.primeAt n) (PrimeFactorUnimodality.prime_primeAt n)
  have hf : Function.Injective f := by
    intro i j hij
    exact PrimeFactorUnimodality.primeAt_strictMono.injective (congrArg Subtype.val hij)
  have hs := summable_prime_reciprocal_sq.comp_injective (i := f) hf
  apply hs.congr
  intro n
  change 1 / (PrimeFactorUnimodality.primeAt n : Real) ^ (2 : Nat) =
    (1 / (PrimeFactorUnimodality.primeAt n : Real)) ^ 2
  rw [div_pow, one_pow]

/-- Full profile equality identifies a permutation when no coordinates vanish. -/
theorem exists_prime_perm_of_positive_profile_eq (a : Nat -> Real)
    (ha : forall n, 0 < a n) (ha1 : forall n, a n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2))
    (heq : Complex.canonicalBernoulliProfile a =
      Complex.canonicalBernoulliProfile reciprocalPrimeProbability) :
    exists e : Equiv.Perm Nat, forall n, a n = reciprocalPrimeProbability (e n) := by
  let ea : Equiv Nat {n : Nat // 0 < a n} :=
    { toFun := fun n => Subtype.mk n (ha n)
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eb : Equiv Nat {n : Nat // 0 < reciprocalPrimeProbability n} :=
    { toFun := fun n => Subtype.mk n (reciprocalPrimeProbability_pos n)
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh := Complex.exists_positive_equiv_of_canonicalBernoulliProfile_eq
    a reciprocalPrimeProbability (fun n => (ha n).le) ha1
    (fun n => (reciprocalPrimeProbability_pos n).le) reciprocalPrimeProbability_le_one
    hsa summable_reciprocalPrimeProbability_sq heq
  let ep := Classical.choose hh
  have hep : forall n : {n : Nat // 0 < a n},
      a n.val = reciprocalPrimeProbability (ep n).val := Classical.choose_spec hh
  let e : Equiv.Perm Nat := ea.trans (ep.trans eb.symm)
  refine Exists.intro e ?_
  intro n
  exact hep (ea n)

def normalizedProbabilityPrefixDefect (a t : Nat -> Real) (n : Nat) : Real :=
  (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
      ((PrimeFactorUnimodality.primeAt n : Real) + t n) / (t n) ^ 2 *
    ((Finset.range (n + 1)).sum (fun i => Real.log (1 + t n * a i) - t n * a i) -
      (Finset.range (n + 1)).sum (primeLogWeight (t n)))

/-- Adaptive accuracy finer than the cubic scale detects every infinite
rearrangement in the positive reciprocal-prime profile class. -/
theorem positive_profile_cutoff_inverse (a : Nat -> Real)
    (ha : forall n, 0 < a n) (ha1 : forall n, a n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2))
    (heq : Complex.canonicalBernoulliProfile a =
      Complex.canonicalBernoulliProfile reciprocalPrimeProbability)
    (t : Nat -> Real) (ht : forall n, 0 < t n) :
    Tendsto (normalizedProbabilityPrefixDefect a t) atTop (nhds 0) <->
      exists N : Nat, exists e : Equiv.Perm Nat,
        (forall n, N <= n -> e n = n) /\
          forall n, a n = reciprocalPrimeProbability (e n) := by
  have hh := exists_prime_perm_of_positive_profile_eq a ha ha1 hsa heq
  let e := Classical.choose hh
  have he : forall n, a n = reciprocalPrimeProbability (e n) := Classical.choose_spec hh
  have hid : normalizedProbabilityPrefixDefect a t = normalizedPrimePrefixDefect e t := by
    funext n
    unfold normalizedProbabilityPrefixDefect normalizedPrimePrefixDefect Finset.prefixDefect
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i]
    simp only [primeLogWeight, reciprocalPrimeProbability, Real.bernoulliLogProfile,
      mul_one_div]
  rw [hid, normalizedPrimePrefixDefect_tendsto_zero_iff e t ht]
  constructor
  . intro h
    exact Exists.intro (Classical.choose h)
      (Exists.intro e (And.intro (Classical.choose_spec h) he))
  . intro h
    let N := Classical.choose h
    let e2 := Classical.choose (Classical.choose_spec h)
    have hd : (forall n, N <= n -> e2 n = n) /\
        forall n, a n = reciprocalPrimeProbability (e2 n) :=
      Classical.choose_spec (Classical.choose_spec h)
    refine Exists.intro N ?_
    intro n hn
    have hp : Function.Injective reciprocalPrimeProbability := by
      intro i j hij
      apply PrimeFactorUnimodality.primeAt_strictMono.injective
      have hv : (PrimeFactorUnimodality.primeAt i : Real) =
          (PrimeFactorUnimodality.primeAt j : Real) := by
        have hi := reciprocalPrimeProbability_pos i
        have hj := reciprocalPrimeProbability_pos j
        unfold reciprocalPrimeProbability at hij hi hj
        have hpi : Not ((PrimeFactorUnimodality.primeAt i : Real) = 0) := by
          exact_mod_cast (PrimeFactorUnimodality.prime_primeAt i).ne_zero
        have hpj : Not ((PrimeFactorUnimodality.primeAt j : Real) = 0) := by
          exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).ne_zero
        field_simp at hij
        linarith only [hij]
      exact_mod_cast hv
    have heqN : e n = e2 n := hp ((he n).symm.trans (hd.2 n))
    exact heqN.trans (hd.1 n hn)

end PrimeFactorOscillations.PrimeProfileRigidity
