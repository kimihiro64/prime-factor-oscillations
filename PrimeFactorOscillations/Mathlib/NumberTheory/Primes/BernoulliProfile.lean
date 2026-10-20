/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.BernoulliProfileZeros

/-!
# Prime-labelled recovery from Bernoulli profile zero sets

Proper rational probabilities with prime denominator retain their prime label.
Consequently, square-summable local root probabilities are recovered at every
prime from their entire compensated profile's zero set alone. No reciprocal
asymptotic, active-prime density, tail ordering, or multiplicity data is needed.
The strict upper bound excludes deterministic successes, which can relabel.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- A positive proper fraction with prime denominator identifies that prime
and its numerator, even against an arbitrary numerator at another prime. -/
theorem eq_of_prime_proper_fraction_eq
    (p q r s : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : 0 < r) (hrp : r < p)
    (heq : (r : Real) / p = (s : Real) / q) :
    And (p = q) (r = s) := by
  have hpR : Not ((p : Real) = 0) := by exact_mod_cast hp.ne_zero
  have hqR : Not ((q : Real) = 0) := by exact_mod_cast hq.ne_zero
  have hcross : r * q = s * p := by
    exact_mod_cast (div_eq_div_iff hpR hqR).mp heq
  have hdiv : Dvd.dvd p (r * q) := by
    rw [hcross]
    exact dvd_mul_left p s
  have hpq : p = q := by
    cases hp.dvd_mul.mp hdiv with
    | inl hpr =>
        exact False.elim ((Nat.not_le_of_gt hrp) (Nat.le_of_dvd hr hpr))
    | inr hpq =>
        exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  refine And.intro hpq ?_
  subst q
  exact Nat.eq_of_mul_eq_mul_right hp.pos hcross

end Nat

namespace Complex

/-- A zero-set inclusion already recovers every positive local root count. -/
theorem prime_counts_eq_of_canonicalBernoulliProfile_zero_imp
    (a b : Nat.Primes -> Nat)
    (ha : forall p, a p < (p : Nat)) (hb : forall p, b p < (p : Nat))
    (hsa : Summable (fun p : Nat.Primes => ((a p : Real) / (p : Nat)) ^ 2))
    (hsb : Summable (fun p : Nat.Primes => ((b p : Real) / (p : Nat)) ^ 2))
    (hzeros : forall z : Complex,
      canonicalBernoulliProfile (fun p : Nat.Primes => (a p : Real) / (p : Nat)) z = 0 ->
      canonicalBernoulliProfile (fun p : Nat.Primes => (b p : Real) / (p : Nat)) z = 0)
    (p : Nat.Primes) (hp : 0 < a p) : a p = b p := by
  let f : Nat.Primes -> Real := fun p => (a p : Real) / (p : Nat)
  let g : Nat.Primes -> Real := fun p => (b p : Real) / (p : Nat)
  have hf0 : forall p, 0 <= f p := fun p =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hg0 : forall p, 0 <= g p := fun p =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hf1 : forall p, f p <= 1 := by
    intro p
    have hden : (0 : Real) < (p : Nat) := by exact_mod_cast p.property.pos
    exact ((div_lt_one hden).mpr (by exact_mod_cast ha p)).le
  have hg1 : forall p, g p <= 1 := by
    intro p
    have hden : (0 : Real) < (p : Nat) := by exact_mod_cast p.property.pos
    exact ((div_lt_one hden).mpr (by exact_mod_cast hb p)).le
  have hfp : Not (f p = 0) := by
    apply ne_of_gt
    apply div_pos
    { exact_mod_cast hp }
    { exact_mod_cast p.property.pos }
  let z : Complex := 1 - 1 / (f p : Complex)
  have hza : canonicalBernoulliProfile f z = 0 :=
    (canonicalBernoulliProfile_eq_zero_iff f hf0 hf1 hsa z).mpr
      (Exists.intro p (And.intro hfp rfl))
  have hzb : canonicalBernoulliProfile g z = 0 := hzeros z hza
  choose q hq using (canonicalBernoulliProfile_eq_zero_iff g hg0 hg1 hsb z).mp hzb
  have hinv : 1 / (f p : Complex) = 1 / (g q : Complex) :=
    sub_right_inj.mp hq.2
  have hfrac : f p = g q := by
    apply Complex.ofReal_injective
    apply inv_injective
    simpa only [one_div] using hinv
  have hmatch := Nat.eq_of_prime_proper_fraction_eq
    (p : Nat) (q : Nat) (a p) (b q) p.property q.property hp (ha p) hfrac
  have hpq : p = q := Subtype.ext hmatch.1
  exact hmatch.2.trans (congrArg b hpq.symm)

/-- The full zero set determines every local root count at its original prime. -/
theorem prime_counts_eq_of_canonicalBernoulliProfile_zero_set_eq
    (a b : Nat.Primes -> Nat)
    (ha : forall p, a p < (p : Nat)) (hb : forall p, b p < (p : Nat))
    (hsa : Summable (fun p : Nat.Primes => ((a p : Real) / (p : Nat)) ^ 2))
    (hsb : Summable (fun p : Nat.Primes => ((b p : Real) / (p : Nat)) ^ 2))
    (hzeros : forall z : Complex,
      canonicalBernoulliProfile (fun p : Nat.Primes => (a p : Real) / (p : Nat)) z = 0 <->
      canonicalBernoulliProfile (fun p : Nat.Primes => (b p : Real) / (p : Nat)) z = 0) :
    a = b := by
  funext p
  by_cases hpa : a p = 0
  { by_cases hpb : b p = 0
    { exact hpa.trans hpb.symm }
    { exact (prime_counts_eq_of_canonicalBernoulliProfile_zero_imp
        b a hb ha hsb hsa (fun z hz => (hzeros z).mpr hz)
        p (Nat.pos_of_ne_zero hpb)).symm } }
  { exact prime_counts_eq_of_canonicalBernoulliProfile_zero_imp
      a b ha hb hsa hsb (fun z hz => (hzeros z).mp hz)
      p (Nat.pos_of_ne_zero hpa) }

/-- Equality of compensated profiles therefore implies exact prime-labelled equality. -/
theorem prime_counts_eq_of_canonicalBernoulliProfile_eq
    (a b : Nat.Primes -> Nat)
    (ha : forall p, a p < (p : Nat)) (hb : forall p, b p < (p : Nat))
    (hsa : Summable (fun p : Nat.Primes => ((a p : Real) / (p : Nat)) ^ 2))
    (hsb : Summable (fun p : Nat.Primes => ((b p : Real) / (p : Nat)) ^ 2))
    (hprofile :
      canonicalBernoulliProfile (fun p : Nat.Primes => (a p : Real) / (p : Nat)) =
      canonicalBernoulliProfile (fun p : Nat.Primes => (b p : Real) / (p : Nat))) :
    a = b := by
  apply prime_counts_eq_of_canonicalBernoulliProfile_zero_set_eq a b ha hb hsa hsb
  intro z
  rw [hprofile]

end Complex
