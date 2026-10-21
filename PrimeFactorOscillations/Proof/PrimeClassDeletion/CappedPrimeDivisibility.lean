/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeClassSamplingActual
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliTailIndicators
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeAffine

/-! # Literal integer-divisibility tail densities at a fixed prime cutoff

The existing complete coefficient error supplies the finite sampling bound.
The prime cutoff is fixed before the sample-size limit is taken.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter
open PrimeFactorOscillations.PrimeClassSampling

noncomputable def finitePrimeTailDensity (s : Finset Nat) (N r : Nat) : Real :=
  (((Finset.Icc 1 N).filter
    (fun n => r <= (s.filter (fun p => Dvd.dvd p n)).card)).card : Real) / (N : Real)

theorem finiteEmpirical_mean_eq (s : Finset Nat) (N : Nat) (phi : Nat -> Real) :
    (Finset.range (s.card + 1)).sum
      (fun k => phi k * (finiteEmpiricalPolynomial s N).coeff k) =
      (1 / (N : Real)) * (Finset.Icc 1 N).sum
        (fun n => phi (s.filter (fun p => Dvd.dvd p n)).card) := by
  classical
  have hc (k : Nat) : (finiteEmpiricalPolynomial s N).coeff k =
      (1 / (N : Real)) * (Finset.Icc 1 N).sum
        (fun n => if (s.filter (fun p => Dvd.dvd p n)).card = k then 1 else 0) := by
    rw [coeff_finiteEmpiricalPolynomial, Finset.sum_boole]
  calc
    _ = (Finset.range (s.card + 1)).sum (fun k =>
        (Finset.Icc 1 N).sum (fun n => (1 / (N : Real)) *
          (phi k * (if (s.filter (fun p => Dvd.dvd p n)).card = k then 1 else 0)))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hc k, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = (Finset.Icc 1 N).sum (fun n =>
        (Finset.range (s.card + 1)).sum (fun k => (1 / (N : Real)) *
          (phi k * (if (s.filter (fun p => Dvd.dvd p n)).card = k then 1 else 0)))) :=
      Finset.sum_comm
    _ = (Finset.Icc 1 N).sum
        (fun n => (1 / (N : Real)) * phi (s.filter (fun p => Dvd.dvd p n)).card) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_eq_single (s.filter (fun p => Dvd.dvd p n)).card]
      next => simp
      next =>
        intro k hk hne
        simp only [Ne.symm hne, ite_false, mul_zero]
      next =>
        intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Finset.card_filter_le _ _))))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem finiteEmpirical_tail_sum_eq_density (s : Finset Nat) (N r : Nat) :
    (Finset.range (s.card + 1)).sum
      (fun k => if r <= k then (finiteEmpiricalPolynomial s N).coeff k else 0) =
        finitePrimeTailDensity s N r := by
  classical
  calc
    _ = (Finset.range (s.card + 1)).sum
        (fun k => (if r <= k then 1 else 0) * (finiteEmpiricalPolynomial s N).coeff k) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : r <= k
      all_goals simp only [h, ite_true, ite_false, one_mul, zero_mul]
    _ = (1 / (N : Real)) * (Finset.Icc 1 N).sum
        (fun n => if r <= (s.filter (fun p => Dvd.dvd p n)).card then 1 else 0) :=
      finiteEmpirical_mean_eq s N _
    _ = _ := by
      rw [Finset.sum_boole]
      unfold finitePrimeTailDensity
      ring

theorem ordinaryReference_coeff_eq_mass (P : Set Nat) (X k : Nat) :
    (finiteReferencePolynomial (primeClassPrefix P X)).coeff k =
      List.bernoulliMass (primeClassCoordinates P (fun p => 1 / (p : Real)) X) k := by
  rw [finiteReferencePolynomial_eq_bernoulli_product,
    <- primeClassCoordinates_probability_product P (fun p : Nat => 1 / (p : Real)) X,
    List.bernoulliProbabilityProduct_coeff]

theorem finiteEmpirical_coefficient_error_le_three (s : Finset Nat)
    (hprime : forall p, Membership.mem s p -> Nat.Prime p)
    (N : Nat) (hN : 0 < N) :
    (Finset.range (s.card + 1)).sum (fun k =>
      abs ((finiteEmpiricalPolynomial s N).coeff k - (finiteReferencePolynomial s).coeff k)) <=
        (3 : Real) ^ s.card / (N : Real) := by
  have h := finiteEmpirical_coefficient_error_le s hprime N hN 0 (le_refl _) zero_le_one
  norm_num only [neg_zero, Real.rpow_zero, mul_one, zero_sub] at h
  simpa only [Polynomial.coeff_sub, Finset.prod_const, Real.rpow_neg_one,
    div_eq_mul_inv, mul_comm] using h

theorem ordinaryPrimeTail_density_error (P : Set Nat) (X N r : Nat) (hN : 0 < N) :
    abs (finitePrimeTailDensity (primeClassPrefix P X) N r -
      primeClassBernoulliTail P (fun p => 1 / (p : Real)) X r) <=
        (3 : Real) ^ (primeClassPrefix P X).card / (N : Real) := by
  rw [primeClassBernoulliTail, List.bernoulliOutcomeTail_eq,
    <- finiteEmpirical_tail_sum_eq_density]
  have hstep :
      abs ((Finset.range ((primeClassPrefix P X).card + 1)).sum
        (fun k => if r <= k then (finiteEmpiricalPolynomial (primeClassPrefix P X) N).coeff k
          else 0) - List.bernoulliTail
            (primeClassCoordinates P (fun p => 1 / (p : Real)) X) r) <=
        (Finset.range ((primeClassPrefix P X).card + 1)).sum (fun k =>
          abs ((finiteEmpiricalPolynomial (primeClassPrefix P X) N).coeff k -
            (finiteReferencePolynomial (primeClassPrefix P X)).coeff k)) := by
    simpa only [primeClassCoordinates_length, <- ordinaryReference_coeff_eq_mass P X] using
      List.abs_bernoulliTail_perturbation_le
        (primeClassCoordinates P (fun p => 1 / (p : Real)) X)
        (fun k => (finiteEmpiricalPolynomial (primeClassPrefix P X) N).coeff k) r
  exact hstep.trans (finiteEmpirical_coefficient_error_le_three (primeClassPrefix P X)
    (fun p hp => primeClassPrefix_prime P X p hp) N hN)

theorem ordinaryPrimeTail_density_tendsto (P : Set Nat) (X r : Nat) :
    Tendsto (fun N : Nat => finitePrimeTailDensity (primeClassPrefix P X) N r)
      atTop (nhds (primeClassBernoulliTail P (fun p => 1 / (p : Real)) X r)) := by
  have hbudget : Tendsto
      (fun N : Nat => (3 : Real) ^ (primeClassPrefix P X).card / (N : Real))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := Real))
  have hdev : Tendsto
      (fun N : Nat => abs (finitePrimeTailDensity (primeClassPrefix P X) N r -
        primeClassBernoulliTail P (fun p => 1 / (p : Real)) X r)) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun N => abs_nonneg _)) ?_ hbudget
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact ordinaryPrimeTail_density_error P X N r (by omega)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hdev

theorem greedyPrimeClass_local_divisibility_limits
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (r : Nat) :
    And (Tendsto (fun N : Nat => finitePrimeTailDensity (primeClassPrefix P (Nat.floor x)) N r)
      atTop (nhds (primeClassBernoulliTail P (fun p => 1 / (p : Real)) (Nat.floor x) r)))
    (And (Tendsto (fun N : Nat =>
        finitePrimeTailDensity (primeClassPrefix greedyPrimeClass (Nat.floor x)) N r)
      atTop (nhds
        (primeClassBernoulliTail greedyPrimeClass (fun p => 1 / (p : Real)) (Nat.floor x) r)))
    (primeClassBernoulliTail P (fun p => 1 / (p : Real)) (Nat.floor x) r <=
      primeClassBernoulliTail greedyPrimeClass (fun p => 1 / (p : Real)) (Nat.floor x) r)) := by
  exact And.intro (ordinaryPrimeTail_density_tendsto P (Nat.floor x) r)
    (And.intro (ordinaryPrimeTail_density_tendsto greedyPrimeClass (Nat.floor x) r)
      ((greedyPrimeClass_local_ordinary_probability P x hx hP).1 r))

end PrimeFactorOscillations.PrimeClassDeletion
