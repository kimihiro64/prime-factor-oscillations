/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.BernoulliProfile

/-!
# Prime-power labels in reciprocal-divisor Bernoulli profiles

Reciprocal-weighted divisors have local odds with prime-power denominator.
Their zero locations retain both the original prime and its exponent.
The canonical compensation is explicit and never changes the zero set.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Nat

/-- A reduced prime-power numerator identifies its prime and exponent. -/
theorem eq_of_reduced_prime_power_ratio_eq
    (p q e f r s : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 0 < e) (_hf : 0 < f)
    (hr : Not (Dvd.dvd p r)) (hs : Not (Dvd.dvd q s))
    (heq : (p : Real) ^ e / r = (q : Real) ^ f / s) :
    And (p = q) (And (e = f) (r = s)) := by
  have hr0 : Not (r = 0) := by intro h; apply hr; rw [h]; exact dvd_zero p
  have hs0 : Not (s = 0) := by intro h; apply hs; rw [h]; exact dvd_zero q
  have hrR : Not ((r : Real) = 0) := by exact_mod_cast hr0
  have hsR : Not ((s : Real) = 0) := by exact_mod_cast hs0
  have hcross : r * q ^ f = s * p ^ e := by
    have hc := (_root_.div_eq_div_iff hrR hsR).mp heq
    exact_mod_cast (by simpa only [mul_comm] using hc.symm :
      (r : Real) * q ^ f = s * p ^ e)
  have hpr : (p ^ e).Coprime r :=
    ((hp.coprime_iff_not_dvd).mpr hr).pow_left e
  have hqs : (q ^ f).Coprime s :=
    ((hq.coprime_iff_not_dvd).mpr hs).pow_left f
  have hdiv1 : Dvd.dvd (p ^ e) (q ^ f) := by
    apply hpr.dvd_of_dvd_mul_left
    rw [hcross]
    exact dvd_mul_left (p ^ e) s
  have hdiv2 : Dvd.dvd (q ^ f) (p ^ e) := by
    apply hqs.dvd_of_dvd_mul_left
    rw [<- hcross]
    exact dvd_mul_left (q ^ f) r
  have hpow : p ^ e = q ^ f := Nat.dvd_antisymm hdiv1 hdiv2
  have hpdiv : Dvd.dvd p (p ^ e) := by
    cases e with
    | zero => omega
    | succ k =>
      rw [pow_succ]
      exact dvd_mul_left p (p ^ k)
  have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp
    (hp.dvd_of_dvd_pow (by rw [<- hpow]; exact hpdiv))
  refine And.intro hpq ?_
  subst q
  have hef : e = f := Nat.pow_right_injective hp.two_le hpow
  refine And.intro hef ?_
  rw [<- hef] at hcross
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos e) hcross

/-- The denominator in a reciprocal-divisor zero, with value zero at exponent zero. -/
def divisorZeroDenominator (p : Nat) : Nat -> Nat
  | 0 => 0
  | a + 1 => 1 + p * divisorZeroDenominator p a

theorem divisorZeroDenominator_pos (p a : Nat) (ha : 0 < a) :
    0 < divisorZeroDenominator p a := by
  cases a with
  | zero => omega
  | succ k => simp only [divisorZeroDenominator]; omega

theorem prime_not_dvd_divisorZeroDenominator (p a : Nat) (hp : Nat.Prime p)
    (ha : 0 < a) : Not (Dvd.dvd p (divisorZeroDenominator p a)) := by
  have hmod : divisorZeroDenominator p a % p = 1 := by
    cases a with
    | zero => omega
    | succ k =>
      simp [divisorZeroDenominator, Nat.add_mod,
        Nat.mod_eq_of_lt hp.one_lt]
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  omega

end Nat

namespace Complex

/-- Success probability for reciprocal-weighted divisors of a prime power. -/
def reciprocalDivisorProbability (p a : Nat) : Real :=
  (Nat.divisorZeroDenominator p a : Real) /
    ((p : Real) ^ a + Nat.divisorZeroDenominator p a)

theorem reciprocalDivisorProbability_nonneg (p a : Nat) (hp : 0 < p) :
    0 <= reciprocalDivisorProbability p a := by
  unfold reciprocalDivisorProbability
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem reciprocalDivisorProbability_le_one (p a : Nat) (hp : 0 < p) :
    reciprocalDivisorProbability p a <= 1 := by
  unfold reciprocalDivisorProbability
  apply (div_le_one (by positivity)).mpr
  exact le_add_of_nonneg_left (by positivity)

/-- The local zero records the full prime-power label, including the exponent. -/
theorem canonicalBernoulliFactor_reciprocalDivisor_eq_zero_iff
    (p a : Nat) (hp : 0 < p) (z : Complex) :
    canonicalBernoulliFactor (reciprocalDivisorProbability p a) z = 0 <->
      And (0 < a)
        (z = -(p : Complex) ^ a / (Nat.divisorZeroDenominator p a : Complex)) := by
  by_cases ha : a = 0
  { subst a
    simp [reciprocalDivisorProbability, Nat.divisorZeroDenominator,
      canonicalBernoulliFactor] }
  have ha0 : 0 < a := Nat.pos_of_ne_zero ha
  have hS : (0 : Real) < Nat.divisorZeroDenominator p a := by
    exact_mod_cast Nat.divisorZeroDenominator_pos p a ha0
  have hpR : (0 : Real) < p := by exact_mod_cast hp
  have hprob : 0 < reciprocalDivisorProbability p a := by
    unfold reciprocalDivisorProbability
    exact div_pos hS (by positivity)
  have hid : (1 : Real) - 1 / reciprocalDivisorProbability p a =
      -(p : Real) ^ a / Nat.divisorZeroDenominator p a := by
    unfold reciprocalDivisorProbability
    field_simp
    ring
  have hidC : (1 : Complex) - 1 / (reciprocalDivisorProbability p a : Complex) =
      -(p : Complex) ^ a / (Nat.divisorZeroDenominator p a : Complex) := by
    exact_mod_cast hid
  rw [canonicalBernoulliFactor_eq_zero_iff, hidC]
  exact and_congr (iff_of_true hprob.ne' ha0) Iff.rfl

/-- The profile for a prime-indexed exponent function under reciprocal divisor weight. -/
def reciprocalDivisorProfile (a : Nat.Primes -> Nat) : Complex -> Complex :=
  canonicalBernoulliProfile
    (fun p : Nat.Primes => reciprocalDivisorProbability (p : Nat) (a p))

theorem reciprocalDivisorProfile_eq_zero_iff (a : Nat.Primes -> Nat)
    (hs : Summable (fun p : Nat.Primes =>
      (reciprocalDivisorProbability (p : Nat) (a p)) ^ 2)) (z : Complex) :
    reciprocalDivisorProfile a z = 0 <->
      exists p : Nat.Primes, And (0 < a p)
        (z = -(p : Complex) ^ (a p) /
          (Nat.divisorZeroDenominator (p : Nat) (a p) : Complex)) := by
  rw [reciprocalDivisorProfile, canonicalBernoulliProfile_eq_zero_iff
    (fun p : Nat.Primes => reciprocalDivisorProbability (p : Nat) (a p))
    (fun p => reciprocalDivisorProbability_nonneg _ _ p.property.pos)
    (fun p => reciprocalDivisorProbability_le_one _ _ p.property.pos) hs z]
  apply exists_congr
  intro p
  exact (canonicalBernoulliFactor_eq_zero_iff
    (reciprocalDivisorProbability (p : Nat) (a p)) z).symm.trans
    (canonicalBernoulliFactor_reciprocalDivisor_eq_zero_iff
      (p : Nat) (a p) p.property.pos z)

/-- Inclusion of profile zero sets preserves each positive exponent exactly. -/
theorem exponent_eq_of_reciprocalDivisorProfile_zero_imp
    (a b : Nat.Primes -> Nat)
    (ha : Summable (fun p : Nat.Primes =>
      (reciprocalDivisorProbability (p : Nat) (a p)) ^ 2))
    (hb : Summable (fun p : Nat.Primes =>
      (reciprocalDivisorProbability (p : Nat) (b p)) ^ 2))
    (hzeros : forall z : Complex,
      reciprocalDivisorProfile a z = 0 -> reciprocalDivisorProfile b z = 0)
    (p : Nat.Primes) (hp : 0 < a p) : a p = b p := by
  let z : Complex := -(p : Complex) ^ (a p) /
    (Nat.divisorZeroDenominator (p : Nat) (a p) : Complex)
  have hz : reciprocalDivisorProfile a z = 0 :=
    (reciprocalDivisorProfile_eq_zero_iff a ha z).mpr
      (Exists.intro p (And.intro hp rfl))
  choose q hq using (reciprocalDivisorProfile_eq_zero_iff b hb z).mp (hzeros z hz)
  have hquotC : (p : Complex) ^ (a p) /
      (Nat.divisorZeroDenominator (p : Nat) (a p) : Complex) =
      (q : Complex) ^ (b q) /
        (Nat.divisorZeroDenominator (q : Nat) (b q) : Complex) := by
    dsimp [z] at hq
    linear_combination -hq.2
  have hquotR : ((p : Nat) : Real) ^ (a p) /
      (Nat.divisorZeroDenominator (p : Nat) (a p) : Real) =
      ((q : Nat) : Real) ^ (b q) /
        (Nat.divisorZeroDenominator (q : Nat) (b q) : Real) := by
    apply Complex.ofReal_injective
    push_cast
    exact hquotC
  have hlabel := Nat.eq_of_reduced_prime_power_ratio_eq
    (p : Nat) (q : Nat) (a p) (b q)
    (Nat.divisorZeroDenominator (p : Nat) (a p))
    (Nat.divisorZeroDenominator (q : Nat) (b q))
    p.property q.property hp hq.1
    (Nat.prime_not_dvd_divisorZeroDenominator (p : Nat) (a p) p.property hp)
    (Nat.prime_not_dvd_divisorZeroDenominator (q : Nat) (b q) q.property hq.1)
    hquotR
  have hpq : p = q := Subtype.ext hlabel.1
  simpa only [<- hpq] using hlabel.2.1

/-- Zero-set inclusion is exactly equality of exponents on the first active support. -/
theorem reciprocalDivisorProfile_zero_imp_iff
    (a b : Nat.Primes -> Nat)
    (ha : Summable (fun p : Nat.Primes =>
      (reciprocalDivisorProbability (p : Nat) (a p)) ^ 2))
    (hb : Summable (fun p : Nat.Primes =>
      (reciprocalDivisorProbability (p : Nat) (b p)) ^ 2)) :
    (forall z : Complex,
      reciprocalDivisorProfile a z = 0 -> reciprocalDivisorProfile b z = 0) <->
      (forall p : Nat.Primes, 0 < a p -> a p = b p) := by
  constructor
  { exact fun h => exponent_eq_of_reciprocalDivisorProfile_zero_imp a b ha hb h }
  { intro h z hz
    choose p hp using (reciprocalDivisorProfile_eq_zero_iff a ha z).mp hz
    apply (reciprocalDivisorProfile_eq_zero_iff b hb z).mpr
    refine Exists.intro p ?_
    rw [<- h p hp.1]
    exact hp }

/-- The entire zero set recovers every prime exponent, including absent primes. -/
theorem reciprocalDivisorProfile_zero_set_eq_iff
    (a b : Nat.Primes -> Nat)
    (ha : Summable (fun p : Nat.Primes =>
      (reciprocalDivisorProbability (p : Nat) (a p)) ^ 2))
    (hb : Summable (fun p : Nat.Primes =>
      (reciprocalDivisorProbability (p : Nat) (b p)) ^ 2)) :
    (forall z : Complex,
      reciprocalDivisorProfile a z = 0 <-> reciprocalDivisorProfile b z = 0) <->
      a = b := by
  constructor
  { intro h
    funext p
    by_cases hp : 0 < a p
    { exact exponent_eq_of_reciprocalDivisorProfile_zero_imp a b ha hb
        (fun z => (h z).mp) p hp }
    { by_cases hbp : 0 < b p
      { have heq := exponent_eq_of_reciprocalDivisorProfile_zero_imp b a hb ha
          (fun z => (h z).mpr) p hbp
        omega }
      { omega } } }
  { intro h
    subst b
    exact fun z => Iff.rfl }

end Complex
