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

end PrimeFactorOscillations.CyclotomicProbability
