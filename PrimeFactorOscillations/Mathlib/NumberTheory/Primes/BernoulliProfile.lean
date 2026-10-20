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

/-- Distinct prime/count labels have an explicit integer-determinant gap. -/
theorem prime_label_zero_separation
    (p q r s : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : 0 < r) (hs : 0 < s) (hrp : r < p)
    (hne : Not (And (p = q) (r = s))) :
    (1 : Real) / ((r : Real) * s) <=
      abs ((1 - (p : Real) / r) - (1 - (q : Real) / s)) := by
  have hp0 : Not ((p : Real) = 0) := by exact_mod_cast hp.ne_zero
  have hq0 : Not ((q : Real) = 0) := by exact_mod_cast hq.ne_zero
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  have hsR : (0 : Real) < s := by exact_mod_cast hs
  have hdet : Not (p * s = q * r) := by
    intro h
    have hcross : r * q = s * p := by
      simpa only [Nat.mul_comm] using h.symm
    apply hne
    apply eq_of_prime_proper_fraction_eq p q r s hp hq hr hrp
    apply (_root_.div_eq_div_iff hp0 hq0).mpr
    exact_mod_cast hcross
  have hunit : (1 : Real) <=
      abs (((p * s : Nat) : Real) - ((q * r : Nat) : Real)) := by
    cases lt_or_gt_of_ne hdet with
    | inl hlt =>
        have hstep : ((p * s : Nat) : Real) + 1 <= ((q * r : Nat) : Real) := by
          exact_mod_cast Nat.succ_le_of_lt hlt
        have hneg : ((p * s : Nat) : Real) - ((q * r : Nat) : Real) < 0 := by
          exact sub_neg.mpr (by exact_mod_cast hlt)
        rw [abs_of_neg hneg]
        linarith
    | inr hgt =>
        have hstep : ((q * r : Nat) : Real) + 1 <= ((p * s : Nat) : Real) := by
          exact_mod_cast Nat.succ_le_of_lt hgt
        have hpos : 0 < ((p * s : Nat) : Real) - ((q * r : Nat) : Real) := by
          exact sub_pos.mpr (by exact_mod_cast hgt)
        rw [abs_of_pos hpos]
        linarith
  have hid : (1 - (p : Real) / r) - (1 - (q : Real) / s) =
      ((q : Real) * r - (p : Real) * s) / ((r : Real) * s) := by
    field_simp [ne_of_gt hrR, ne_of_gt hsR]
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hrR hsR)]
  apply _root_.div_le_div_of_nonneg_right _ (mul_pos hrR hsR).le
  simpa only [Nat.cast_mul, abs_sub_comm] using hunit

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

/-- Explicit zero locations for proper integer-over-prime local probabilities. -/
theorem canonicalBernoulliProfile_prime_counts_eq_zero_iff
    (a : Nat.Primes -> Nat) (ha : forall p, a p < (p : Nat))
    (hs : Summable (fun p : Nat.Primes => ((a p : Real) / (p : Nat)) ^ 2))
    (z : Complex) :
    canonicalBernoulliProfile (fun p : Nat.Primes => (a p : Real) / (p : Nat)) z = 0 <->
      exists p : Nat.Primes, And (0 < a p)
        (z = 1 - (p : Nat) / (a p : Complex)) := by
  have h0 : forall p : Nat.Primes, 0 <= (a p : Real) / (p : Nat) :=
    fun p => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h1 : forall p : Nat.Primes, (a p : Real) / (p : Nat) <= 1 := by
    intro p
    exact ((div_lt_one (by exact_mod_cast p.property.pos)).mpr
      (by exact_mod_cast ha p)).le
  rw [canonicalBernoulliProfile_eq_zero_iff _ h0 h1 hs z]
  constructor
  { intro h
    choose p hp using h
    have hpos : 0 < a p := Nat.pos_of_ne_zero (fun hzero => hp.1 (by simp [hzero]))
    refine Exists.intro p (And.intro hpos ?_)
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast, one_div_div] using hp.2 }
  { intro h
    choose p hp using h
    refine Exists.intro p (And.intro ?_ ?_)
    { exact ne_of_gt (div_pos (by exact_mod_cast hp.1)
        (by exact_mod_cast p.property.pos)) }
    { simpa only [Complex.ofReal_div, Complex.ofReal_natCast, one_div_div] using hp.2 } }

/-- Two profiles share a zero exactly at an agreeing positive prime coordinate. -/
theorem canonicalBernoulliProfile_prime_counts_common_zero_iff
    (a b : Nat.Primes -> Nat)
    (ha : forall p, a p < (p : Nat)) (hb : forall p, b p < (p : Nat))
    (hsa : Summable (fun p : Nat.Primes => ((a p : Real) / (p : Nat)) ^ 2))
    (hsb : Summable (fun p : Nat.Primes => ((b p : Real) / (p : Nat)) ^ 2))
    (z : Complex) :
    And (canonicalBernoulliProfile (fun p : Nat.Primes => (a p : Real) / (p : Nat)) z = 0)
      (canonicalBernoulliProfile (fun p : Nat.Primes => (b p : Real) / (p : Nat)) z = 0) <->
      exists p : Nat.Primes, And (0 < a p) (And (a p = b p)
        (z = 1 - (p : Nat) / (a p : Complex))) := by
  constructor
  { intro h
    choose p hp using (canonicalBernoulliProfile_prime_counts_eq_zero_iff
      a ha hsa z).mp h.1
    choose q hq using (canonicalBernoulliProfile_prime_counts_eq_zero_iff
      b hb hsb z).mp h.2
    have heq : (p : Nat) / (a p : Complex) = (q : Nat) / (b q : Complex) :=
      sub_right_inj.mp (hp.2.symm.trans hq.2)
    have hfrac : (a p : Real) / (p : Nat) = (b q : Real) / (q : Nat) := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_div, Complex.ofReal_natCast, inv_div] using
        congrArg Inv.inv heq
    have hmatch := Nat.eq_of_prime_proper_fraction_eq
      (p : Nat) (q : Nat) (a p) (b q) p.property q.property hp.1 (ha p) hfrac
    have hpq : p = q := Subtype.ext hmatch.1
    subst q
    exact Exists.intro p (And.intro hp.1 (And.intro hmatch.2 hp.2)) }
  { intro h
    choose p hp using h
    refine And.intro
      ((canonicalBernoulliProfile_prime_counts_eq_zero_iff a ha hsa z).mpr
        (Exists.intro p (And.intro hp.1 hp.2.2))) ?_
    apply (canonicalBernoulliProfile_prime_counts_eq_zero_iff b hb hsb z).mpr
    rw [hp.2.1] at hp
    exact Exists.intro p (And.intro hp.1 hp.2.2) }

/-- A bounded local root count gives a height-independent profile-zero gap. -/
theorem prime_label_zero_separation_bounded
    (D p q r s : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : 0 < r) (hs : 0 < s) (hrp : r < p)
    (hrD : r <= D) (hsD : s <= D)
    (hne : Not (And (p = q) (r = s))) :
    (1 : Real) / (D : Real) ^ 2 <=
      dist (1 - (p : Complex) / r) (1 - (q : Complex) / s) := by
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  have hsR : (0 : Real) < s := by exact_mod_cast hs
  have hprod : (r : Real) * s <= (D : Real) ^ 2 := by
    rw [pow_two]
    exact_mod_cast Nat.mul_le_mul hrD hsD
  have hsep := Nat.prime_label_zero_separation p q r s hp hq hr hs hrp hne
  have hsepC : (1 : Real) / ((r : Real) * s) <=
      dist (1 - (p : Complex) / r) (1 - (q : Complex) / s) := by
    simpa only [dist_eq_norm, <- Complex.ofReal_natCast, <- Complex.ofReal_one,
      <- Complex.ofReal_div, <- Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hsep
  exact (div_le_div_of_nonneg_left zero_le_one (mul_pos hrR hsR) hprod).trans hsepC

/-- A noisy zero location within half the gap has a unique prime/count label. -/
theorem prime_label_eq_of_close_zero_locations
    (D p q r s : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : 0 < r) (hs : 0 < s) (hrp : r < p)
    (hrD : r <= D) (hsD : s <= D) (u : Complex)
    (hu : dist u (1 - (p : Complex) / r) < 1 / (2 * (D : Real) ^ 2))
    (hv : dist u (1 - (q : Complex) / s) < 1 / (2 * (D : Real) ^ 2)) :
    And (p = q) (r = s) := by
  by_contra hne
  have hsep := prime_label_zero_separation_bounded D p q r s hp hq hr hs hrp hrD hsD hne
  have htriangle := dist_triangle (1 - (p : Complex) / r) u
    (1 - (q : Complex) / s)
  rw [dist_comm (1 - (p : Complex) / r) u] at htriangle
  have hD : (0 : Real) < D := by exact_mod_cast Nat.lt_of_lt_of_le hr hrD
  have hhalf : (1 : Real) / (2 * (D : Real) ^ 2) +
      1 / (2 * (D : Real) ^ 2) = 1 / (D : Real) ^ 2 := by
    field_simp [ne_of_gt hD]
    ring
  linarith

/-- The same separation holds between zeros from any two bounded-count profiles. -/
theorem canonicalBernoulliProfile_prime_zeros_separated
    (D : Nat) (a b : Nat.Primes -> Nat)
    (ha : forall p, a p < (p : Nat)) (hb : forall p, b p < (p : Nat))
    (hDa : forall p, a p <= D) (hDb : forall p, b p <= D)
    (hsa : Summable (fun p : Nat.Primes => ((a p : Real) / (p : Nat)) ^ 2))
    (hsb : Summable (fun p : Nat.Primes => ((b p : Real) / (p : Nat)) ^ 2))
    (z w : Complex)
    (hz : canonicalBernoulliProfile (fun p : Nat.Primes => (a p : Real) / (p : Nat)) z = 0)
    (hw : canonicalBernoulliProfile (fun p : Nat.Primes => (b p : Real) / (p : Nat)) w = 0)
    (hne : Not (z = w)) :
    (1 : Real) / (D : Real) ^ 2 <= dist z w := by
  choose p hp using (canonicalBernoulliProfile_prime_counts_eq_zero_iff a ha hsa z).mp hz
  choose q hq using (canonicalBernoulliProfile_prime_counts_eq_zero_iff b hb hsb w).mp hw
  have hlabels : Not (And ((p : Nat) = (q : Nat)) (a p = b q)) := by
    intro h
    apply hne
    calc
      z = 1 - (p : Nat) / (a p : Complex) := hp.2
      _ = 1 - (q : Nat) / (b q : Complex) := by rw [h.1, h.2]
      _ = w := hq.2.symm
  rw [hp.2, hq.2]
  exact prime_label_zero_separation_bounded D (p : Nat) (q : Nat) (a p) (b q)
    p.property q.property hp.1 hq.1 (ha p) (hDa p) (hDb q) hlabels

end Complex
