/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingCoefficient

/-!
# The actual finite empirical law and its Bernoulli reference

The empirical polynomial samples every integer from one through N. Its
reference is exactly the finite Bernoulli product. Their difference is the
complete signed floor-error polynomial, so the uniform coefficient estimate
applies to the actual sample without a model-error assumption.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

noncomputable def finiteEmpiricalPolynomial (s : Finset Nat) (N : Nat) :
    Polynomial Real :=
  Polynomial.C (1 / (N : Real)) *
    (Finset.Icc 1 N).sum (fun m =>
      Polynomial.X ^ (s.filter (fun p => Dvd.dvd p m)).card)

noncomputable def finiteReferencePolynomial (s : Finset Nat) : Polynomial Real :=
  s.powerset.sum (fun t =>
    Polynomial.C (1 / ((t.prod (fun p => p) : Nat) : Real)) *
      (Polynomial.X - 1) ^ t.card)

theorem finiteEmpiricalPolynomial_eq_subset_sum
    (s : Finset Nat) (hprime : forall p, Membership.mem s p -> Nat.Prime p)
    (N : Nat) :
    finiteEmpiricalPolynomial s N =
      s.powerset.sum (fun t =>
        Polynomial.C (((N / t.prod (fun p => p) : Nat) : Real) / (N : Real)) *
          (Polynomial.X - 1) ^ t.card) := by
  unfold finiteEmpiricalPolynomial
  rw [finitePrimeSupport_sampling_identity s hprime N (Polynomial.X : Polynomial Real),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [div_eq_mul_inv, one_mul, Polynomial.C_mul, map_natCast]
  ring

theorem finiteEmpirical_sub_reference_eq_error
    (s : Finset Nat) (hprime : forall p, Membership.mem s p -> Nat.Prime p)
    (N : Nat) :
    finiteEmpiricalPolynomial s N - finiteReferencePolynomial s =
      finiteSamplingErrorPolynomial s N := by
  rw [finiteEmpiricalPolynomial_eq_subset_sum s hprime N]
  unfold finiteReferencePolynomial finiteSamplingErrorPolynomial
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Polynomial.C_sub]
  ring

theorem prod_inverse_primeConstants (s : Finset Nat) :
    s.prod (fun p => Polynomial.C (1 / (p : Real))) =
      Polynomial.C (1 / ((s.prod (fun p => p) : Nat) : Real)) := by
  rw [<- map_prod]
  congr 1
  simp only [one_div, Finset.prod_inv_distrib, Nat.cast_prod]

theorem finiteReferencePolynomial_eq_bernoulli_product (s : Finset Nat) :
    finiteReferencePolynomial s =
      s.prod (fun p => Polynomial.C (1 - 1 / (p : Real)) +
        Polynomial.C (1 / (p : Real)) * Polynomial.X) := by
  have hfactor : forall p : Nat,
      Polynomial.C (1 - 1 / (p : Real)) +
          Polynomial.C (1 / (p : Real)) * Polynomial.X =
        Polynomial.C (1 / (p : Real)) * (Polynomial.X - 1) + 1 := by
    intro p
    rw [Polynomial.C_sub, Polynomial.C_1]
    ring
  calc
    finiteReferencePolynomial s =
        s.powerset.sum (fun t => t.prod (fun p =>
          Polynomial.C (1 / (p : Real)) * (Polynomial.X - 1))) := by
      unfold finiteReferencePolynomial
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.prod_mul_distrib, Finset.prod_const, prod_inverse_primeConstants]
    _ = s.prod (fun p =>
        Polynomial.C (1 / (p : Real)) * (Polynomial.X - 1) + 1) :=
      (Finset.prod_add_one s).symm
    _ = s.prod (fun p => Polynomial.C (1 - 1 / (p : Real)) +
        Polynomial.C (1 / (p : Real)) * Polynomial.X) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (hfactor p).symm

theorem finiteEmpirical_coefficient_error_le
    (s : Finset Nat) (hprime : forall p, Membership.mem s p -> Nat.Prime p)
    (N : Nat) (hN : 0 < N) (sigma : Real)
    (hs0 : 0 <= sigma) (hs1 : sigma <= 1) :
    (Finset.range (s.card + 1)).sum (fun k =>
      abs ((finiteEmpiricalPolynomial s N - finiteReferencePolynomial s).coeff k)) <=
        (N : Real) ^ (sigma - 1) *
          s.prod (fun p => 1 + 2 * (p : Real) ^ (-sigma)) := by
  rw [finiteEmpirical_sub_reference_eq_error s hprime N]
  exact sum_abs_coeff_finiteSamplingError_le s hprime N hN sigma hs0 hs1

theorem finiteEmpirical_bernoulli_coefficient_error_le
    (s : Finset Nat) (hprime : forall p, Membership.mem s p -> Nat.Prime p)
    (N : Nat) (hN : 0 < N) (sigma : Real)
    (hs0 : 0 <= sigma) (hs1 : sigma <= 1) :
    (Finset.range (s.card + 1)).sum (fun k =>
      abs ((finiteEmpiricalPolynomial s N -
        s.prod (fun p => Polynomial.C (1 - 1 / (p : Real)) +
          Polynomial.C (1 / (p : Real)) * Polynomial.X)).coeff k)) <=
        (N : Real) ^ (sigma - 1) *
          s.prod (fun p => 1 + 2 * (p : Real) ^ (-sigma)) := by
  rw [<- finiteReferencePolynomial_eq_bernoulli_product]
  exact finiteEmpirical_coefficient_error_le s hprime N hN sigma hs0 hs1

end PrimeFactorOscillations.PrimeClassSampling
