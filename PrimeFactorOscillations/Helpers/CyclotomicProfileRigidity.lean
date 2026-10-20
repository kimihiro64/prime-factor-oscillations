/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CyclotomicProbability
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.BernoulliProfile

/-!
# Exact recovery of cyclotomic local root counts

The canonical compensated Bernoulli profile uses the actual success
probabilities count(q,p)/p, centred at one. It is entire and determines all
these counts at their original prime labels. This normalization is explicit;
no equality with a differently compensated PrimeClockLaw profile is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CyclotomicProbability

theorem probability_le_totient_primeWeight (q : Nat) (p : Nat.Primes) :
    probability q p <= (Nat.totient q : Real) * primeProfileWeight (p : Nat) := by
  have hp : (0 : Real) < (p : Nat) := by exact_mod_cast p.property.pos
  have hpred : (0 : Real) < (((p : Nat) - 1 : Nat) : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt p.property.one_lt
  have hpredle : (((p : Nat) - 1 : Nat) : Real) <= ((p : Nat) : Real) := by
    exact_mod_cast Nat.sub_le (p : Nat) 1
  have hc : (count q p : Real) <= (Nat.totient q : Real) := by
    exact_mod_cast count_le_totient q p
  change (count q p : Real) / (p : Nat) <=
    (Nat.totient q : Real) * (1 / (((p : Nat) - 1 : Nat) : Real))
  calc
    (count q p : Real) / (p : Nat) <= (Nat.totient q : Real) / (p : Nat) :=
      div_le_div_of_nonneg_right hc hp.le
    _ <= (Nat.totient q : Real) / (((p : Nat) - 1 : Nat) : Real) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpred hpredle
    _ = (Nat.totient q : Real) *
        (1 / (((p : Nat) - 1 : Nat) : Real)) := by ring

theorem summable_probability_sq (q : Nat) :
    Summable (fun p : Nat.Primes => (probability q p) ^ 2) := by
  apply (summable_primeProfileWeight_sq.mul_left
    ((Nat.totient q : Real) ^ 2)).of_nonneg_of_le
    (fun p => sq_nonneg (probability q p))
  intro p
  have hb := probability_le_totient_primeWeight q p
  have hs := mul_self_le_mul_self (probability_nonneg q p) hb
  simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using hs

/-- Canonical Bernoulli compensation by the actual success probabilities. -/
def bernoulliProfile (q : Nat) : Complex -> Complex :=
  Complex.canonicalBernoulliProfile (probability q)

theorem differentiable_bernoulliProfile (q : Nat) :
    Differentiable Complex (bernoulliProfile q) :=
  Complex.differentiable_canonicalBernoulliProfile (probability q)
    (probability_nonneg q) (fun p => (probability_lt_one q p).le)
    (summable_probability_sq q)

/-- Equal zero sets recover all depleted local root counts, including zeros. -/
theorem count_eq_of_bernoulliProfile_zero_set_eq (q r : Nat)
    (hzeros : forall z : Complex,
      bernoulliProfile q z = 0 <-> bernoulliProfile r z = 0) :
    count q = count r :=
  Complex.prime_counts_eq_of_canonicalBernoulliProfile_zero_set_eq
    (count q) (count r) (count_lt_prime q) (count_lt_prime r)
    (summable_probability_sq q) (summable_probability_sq r) hzeros

theorem count_eq_of_bernoulliProfile_eq (q r : Nat)
    (hprofile : bernoulliProfile q = bernoulliProfile r) :
    count q = count r :=
  Complex.prime_counts_eq_of_canonicalBernoulliProfile_eq
    (count q) (count r) (count_lt_prime q) (count_lt_prime r)
    (summable_probability_sq q) (summable_probability_sq r) hprofile

/-- The intrinsic entire profile is a complete fingerprint of the local law. -/
theorem bernoulliProfile_eq_iff_count_eq (q r : Nat) :
    bernoulliProfile q = bernoulliProfile r <-> count q = count r := by
  constructor
  { exact count_eq_of_bernoulliProfile_eq q r }
  { intro h
    unfold bernoulliProfile probability
    rw [h] }

/-- A positive depleted cyclotomic count always equals the degree. -/
theorem count_eq_totient_of_pos (q : Nat) (p : Nat.Primes)
    (hp : 0 < count q p) : count q p = Nat.totient q := by
  classical
  have hf := count_formula q p
  split_ifs at hf <;> omega

/-- Identity-class membership is exactly the positive local-count condition. -/
theorem count_pos_iff (q : Nat) (hq : 2 <= q) (p : Nat.Primes) :
    0 < count q p <-> Dvd.dvd q ((p : Nat) - 1) := by
  classical
  constructor
  { intro h
    by_contra hn
    have hz : count q p = 0 := by
      rw [count_formula]
      by_cases hpq : Dvd.dvd (p : Nat) q
      { exact ite_eq_left hpq }
      { rw [ite_eq_right hpq, ite_eq_right hn] }
    omega }
  { intro h
    have hpred : 0 < (p : Nat) - 1 := Nat.sub_pos_of_lt p.property.one_lt
    have hqle := Nat.le_of_dvd hpred h
    have hpq : Not (Dvd.dvd (p : Nat) q) := by
      intro hpq
      have hple := Nat.le_of_dvd (by omega : 0 < q) hpq
      omega
    rw [count_formula, ite_eq_right hpq, ite_eq_left h]
    exact Nat.totient_pos.mpr (by omega) }

/-- The full zero set is an explicitly scaled prime progression. -/
theorem bernoulliProfile_eq_zero_iff (q : Nat) (hq : 2 <= q) (z : Complex) :
    bernoulliProfile q z = 0 <->
      exists p : Nat.Primes, And (Dvd.dvd q ((p : Nat) - 1))
        (z = 1 - (p : Nat) / (Nat.totient q : Complex)) := by
  change Complex.canonicalBernoulliProfile
    (fun p : Nat.Primes => (count q p : Real) / (p : Nat)) z = 0 <-> _
  rw [Complex.canonicalBernoulliProfile_prime_counts_eq_zero_iff
    (count q) (count_lt_prime q) (summable_probability_sq q) z]
  constructor
  { intro h
    choose p hp using h
    refine Exists.intro p (And.intro ((count_pos_iff q hq p).mp hp.1) ?_)
    rw [count_eq_totient_of_pos q p hp.1] at hp
    exact hp.2 }
  { intro h
    choose p hp using h
    have hpos := (count_pos_iff q hq p).mpr hp.1
    refine Exists.intro p (And.intro hpos ?_)
    rw [count_eq_totient_of_pos q p hpos]
    exact hp.2 }

/-- Shared zeros require equal degrees; their prime labels lie in the lcm class. -/
theorem bernoulliProfile_common_zero_iff
    (q r : Nat) (hq : 2 <= q) (hr : 2 <= r) (z : Complex) :
    And (bernoulliProfile q z = 0) (bernoulliProfile r z = 0) <->
      And (Nat.totient q = Nat.totient r)
        (exists p : Nat.Primes, And (Dvd.dvd (Nat.lcm q r) ((p : Nat) - 1))
          (z = 1 - (p : Nat) / (Nat.totient q : Complex))) := by
  constructor
  { intro h
    have hz : And
        (Complex.canonicalBernoulliProfile
          (fun p : Nat.Primes => (count q p : Real) / (p : Nat)) z = 0)
        (Complex.canonicalBernoulliProfile
          (fun p : Nat.Primes => (count r p : Real) / (p : Nat)) z = 0) := h
    choose p hp using
      (Complex.canonicalBernoulliProfile_prime_counts_common_zero_iff
        (count q) (count r) (count_lt_prime q) (count_lt_prime r)
        (summable_probability_sq q) (summable_probability_sq r) z).mp hz
    have hposr : 0 < count r p := by rw [<- hp.2.1]; exact hp.1
    have hcountq := count_eq_totient_of_pos q p hp.1
    have hcountr := count_eq_totient_of_pos r p hposr
    refine And.intro (hcountq.symm.trans (hp.2.1.trans hcountr)) ?_
    refine Exists.intro p (And.intro ?_ ?_)
    { exact Nat.lcm_dvd_iff.mpr (And.intro
        ((count_pos_iff q hq p).mp hp.1) ((count_pos_iff r hr p).mp hposr)) }
    { rw [hcountq] at hp
      exact hp.2.2 } }
  { intro h
    choose p hp using h.2
    have hdiv := Nat.lcm_dvd_iff.mp hp.1
    refine And.intro ((bernoulliProfile_eq_zero_iff q hq z).mpr
      (Exists.intro p (And.intro hdiv.1 hp.2))) ?_
    apply (bernoulliProfile_eq_zero_iff r hr z).mpr
    refine Exists.intro p (And.intro hdiv.2 ?_)
    rw [<- h.1]
    exact hp.2 }

/-- Different totients force disjoint zero sets, despite overlaps of prime classes. -/
theorem bernoulliProfile_no_common_zero_of_totient_ne
    (q r : Nat) (hq : 2 <= q) (hr : 2 <= r)
    (hphi : Not (Nat.totient q = Nat.totient r)) (z : Complex) :
    Not (And (bernoulliProfile q z = 0) (bernoulliProfile r z = 0)) := by
  intro h
  exact hphi ((bernoulliProfile_common_zero_iff q r hq hr z).mp h).1

end PrimeFactorOscillations.CyclotomicProbability
