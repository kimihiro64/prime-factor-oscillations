/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Topology.Algebra.InfiniteSum.Order
import PrimeFactorOscillations.Helpers.PrimeClassSamplingActual

/-!
# A coefficient-error constant independent of the finite prime cutoff

The complete finite Bernoulli budget is bounded by the convergent power sum
of one fixed prime class. The resulting estimate is uniform for every
positive sample size N and every prime cutoff Y at least N.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.PrimeClassDecoder

noncomputable def classPowerWeight (P : Set Nat) (sigma : Real) (p : Nat) : Real := by
  classical
  exact if And (Nat.Prime p) (Membership.mem P p) then
    (p : Real) ^ (-sigma) else 0

theorem classPowerWeight_nonneg (P : Set Nat) (sigma : Real) (p : Nat) :
    0 <= classPowerWeight P sigma p := by
  classical
  unfold classPowerWeight
  split_ifs
  case pos => exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  case neg => exact le_refl 0

theorem classPowerWeight_on_prefix
    (P : Set Nat) (sigma : Real) (Y p : Nat)
    (hp : Membership.mem (primeClassPrefix P Y) p) :
    classPowerWeight P sigma p = (p : Real) ^ (-sigma) := by
  classical
  unfold classPowerWeight
  exact ite_eq_left (Finset.mem_filter.mp hp).2

theorem primeClassPrefix_powerSum_le
    (P : Set Nat) (sigma : Real) (Y : Nat)
    (hsum : Summable (classPowerWeight P sigma)) :
    (primeClassPrefix P Y).sum (fun p => (p : Real) ^ (-sigma)) <=
      tsum (classPowerWeight P sigma) := by
  calc
    (primeClassPrefix P Y).sum (fun p => (p : Real) ^ (-sigma)) =
        (primeClassPrefix P Y).sum (classPowerWeight P sigma) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (classPowerWeight_on_prefix P sigma Y p hp).symm
    _ <= tsum (classPowerWeight P sigma) :=
      Summable.sum_le_tsum (primeClassPrefix P Y)
        (fun p hp => classPowerWeight_nonneg P sigma p) hsum

theorem prod_one_add_two_rpow_le_exp (s : Finset Nat) (sigma : Real) :
    s.prod (fun p => 1 + 2 * (p : Real) ^ (-sigma)) <=
      Real.exp (2 * s.sum (fun p => (p : Real) ^ (-sigma))) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
      rw [Finset.prod_insert hps, Finset.sum_insert hps, mul_add, Real.exp_add]
      have hlocal : 1 + 2 * (p : Real) ^ (-sigma) <=
          Real.exp (2 * (p : Real) ^ (-sigma)) := by
        simpa only [add_comm] using Real.add_one_le_exp (2 * (p : Real) ^ (-sigma))
      have hprodnonneg : 0 <= s.prod (fun q => 1 + 2 * (q : Real) ^ (-sigma)) := by
        apply Finset.prod_nonneg
        intro q hq
        exact add_nonneg zero_le_one
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg q) _))
      exact mul_le_mul hlocal ih hprodnonneg (le_of_lt (Real.exp_pos _))

theorem primeClassPrefix_budget_le_exp
    (P : Set Nat) (sigma : Real) (Y : Nat)
    (hsum : Summable (classPowerWeight P sigma)) :
    (primeClassPrefix P Y).prod (fun p => 1 + 2 * (p : Real) ^ (-sigma)) <=
      Real.exp (2 * tsum (classPowerWeight P sigma)) := by
  apply (prod_one_add_two_rpow_le_exp (primeClassPrefix P Y) sigma).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left
    (primeClassPrefix_powerSum_le P sigma Y hsum) (by norm_num)

theorem actualSample_coefficient_error_le_exp
    (P : Set Nat) (N Y : Nat) (hNY : N <= Y) (hN : 0 < N)
    (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    (Finset.range ((primeClassPrefix P Y).card + 1)).sum (fun k =>
      abs ((sampleCount P N k : Real) / (N : Real) -
        (finiteReferencePolynomial (primeClassPrefix P Y)).coeff k)) <=
      (N : Real) ^ (sigma - 1) * Real.exp (2 * tsum (classPowerWeight P sigma)) := by
  apply (actualSample_coefficient_error_le P N Y hNY hN sigma hs0 hs1).trans
  exact mul_le_mul_of_nonneg_left (primeClassPrefix_budget_le_exp P sigma Y hsum)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)

end PrimeFactorOscillations.PrimeClassSampling
