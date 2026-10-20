/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.BernoulliDivisorProfile

/-!
# Exact integer recovery from reciprocal-divisor profile zeros

A positive integer supplies a finitely supported exponent function, so the
general profile inverse requires no analytic hypothesis in this application.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

/-- The canonical reciprocal-divisor profile of the full factorization of n. -/
def reciprocalDivisorIntegerProfile (n : Nat) : Complex -> Complex :=
  reciprocalDivisorProfile (fun p : Nat.Primes => n.factorization (p : Nat))

theorem summable_reciprocalDivisorIntegerProbability_sq (n : Nat) :
    Summable (fun p : Nat.Primes =>
      (reciprocalDivisorProbability (p : Nat) (n.factorization (p : Nat))) ^ 2) := by
  have hs : Function.HasFiniteSupport (fun p : Nat =>
      (reciprocalDivisorProbability p (n.factorization p)) ^ 2) := by
    apply n.factorization.hasFiniteSupport.subset
    intro p hp
    change Not (n.factorization p = 0)
    intro hzero
    apply hp
    simp [hzero, reciprocalDivisorProbability, Nat.divisorZeroDenominator]
  exact (summable_of_hasFiniteSupport hs).comp_injective Subtype.val_injective

/-- No summability assumption remains for actual finite integer factorizations. -/
theorem reciprocalDivisorIntegerProfile_zero_imp_iff (n m : Nat) :
    (forall z : Complex, reciprocalDivisorIntegerProfile n z = 0 ->
      reciprocalDivisorIntegerProfile m z = 0) <->
      (forall p : Nat.Primes, 0 < n.factorization (p : Nat) ->
        n.factorization (p : Nat) = m.factorization (p : Nat)) :=
  reciprocalDivisorProfile_zero_imp_iff _ _
    (summable_reciprocalDivisorIntegerProbability_sq n)
    (summable_reciprocalDivisorIntegerProbability_sq m)

/-- The zero set alone identifies a positive integer, including every exponent. -/
theorem reciprocalDivisorIntegerProfile_zero_set_eq_iff (n m : Nat)
    (hn : 0 < n) (hm : 0 < m) :
    (forall z : Complex, reciprocalDivisorIntegerProfile n z = 0 <->
      reciprocalDivisorIntegerProfile m z = 0) <-> n = m := by
  constructor
  { intro h
    have hfun := (reciprocalDivisorProfile_zero_set_eq_iff
      (fun p : Nat.Primes => n.factorization (p : Nat))
      (fun p : Nat.Primes => m.factorization (p : Nat))
      (summable_reciprocalDivisorIntegerProbability_sq n)
      (summable_reciprocalDivisorIntegerProbability_sq m)).mp h
    apply Nat.factorization_inj hn.ne' hm.ne'
    ext p
    by_cases hp : Nat.Prime p
    { exact congrFun hfun (Subtype.mk p hp) }
    { rw [Nat.factorization_eq_zero_of_not_prime n hp,
        Nat.factorization_eq_zero_of_not_prime m hp] } }
  { intro h
    subst m
    exact fun z => Iff.rfl }

/-- Spectral inclusion is exactly unitary divisibility of positive integers. -/
theorem reciprocalDivisorIntegerProfile_zero_imp_iff_unitary
    (n m : Nat) (hn : 0 < n) (hm : 0 < m) :
    (forall z : Complex, reciprocalDivisorIntegerProfile n z = 0 ->
      reciprocalDivisorIntegerProfile m z = 0) <->
      exists k : Nat, And (m = n * k) (Nat.Coprime n k) := by
  rw [reciprocalDivisorIntegerProfile_zero_imp_iff]
  constructor
  { intro h
    have hle : n.factorization <= m.factorization := by
      intro p
      by_cases hp : Nat.Prime p
      { by_cases he : 0 < n.factorization p
        { exact (h (Subtype.mk p hp) he).le }
        { omega } }
      { rw [Nat.factorization_eq_zero_of_not_prime n hp]
        exact Nat.zero_le _ }
    have hd := (Nat.factorization_le_iff_dvd hn.ne' hm.ne').mp hle
    choose k hk using hd
    have hk0 : Not (k = 0) := by
      intro hz
      rw [hz, Nat.mul_zero] at hk
      omega
    have hmul : m.factorization = n.factorization + k.factorization := by
      rw [hk, Nat.factorization_mul hn.ne' hk0]
    refine Exists.intro k (And.intro hk ?_)
    apply Nat.coprime_iff_gcd_eq_one.mpr
    have hg0 : Not (Nat.gcd n k = 0) := by
      intro hz
      have hd0 := Nat.gcd_dvd_left n k
      have hn0 : n = 0 := by simpa [hz] using hd0
      omega
    apply Nat.factorization_inj hg0 (by decide : Not ((1 : Nat) = 0))
    rw [Nat.factorization_gcd hn.ne' hk0, Nat.factorization_one]
    ext p
    change min (n.factorization p) (k.factorization p) = 0
    by_cases hp : Nat.Prime p
    { by_cases he : 0 < n.factorization p
      { have heq := h (Subtype.mk p hp) he
        change n.factorization p = m.factorization p at heq
        have hpoint := congrArg (fun f : Finsupp Nat Nat => f p) hmul
        change m.factorization p = n.factorization p + k.factorization p at hpoint
        have hkzero : k.factorization p = 0 := by omega
        simp [hkzero] }
      { have hnzero : n.factorization p = 0 := by omega
        simp [hnzero] } }
    { simp [Nat.factorization_eq_zero_of_not_prime n hp] } }
  { intro h
    choose k hk using h
    have hk0 : Not (k = 0) := by
      intro hz
      have hmk := hk.1
      rw [hz, Nat.mul_zero] at hmk
      omega
    intro p he
    have hpn : Dvd.dvd (p : Nat) n := by
      by_contra hd
      have hz := Nat.factorization_eq_zero_of_not_dvd hd
      omega
    have hpk : Not (Dvd.dvd (p : Nat) k) :=
      p.property.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hpn hk.2)
    have hkzero := Nat.factorization_eq_zero_of_not_dvd hpk
    rw [hk.1, Nat.factorization_mul hn.ne' hk0]
    change n.factorization (p : Nat) =
      n.factorization (p : Nat) + k.factorization (p : Nat)
    rw [hkzero, Nat.add_zero] }

end Complex
