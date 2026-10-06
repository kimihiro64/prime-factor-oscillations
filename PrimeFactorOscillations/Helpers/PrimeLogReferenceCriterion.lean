/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.FamilyNicolasTransfer

/-!
# A general local-product qualification theorem

Only positivity and a convergent normalized local logarithmic prefix are
required. The qualification condition contains neither theta nor RH. The
quadratic law is a concrete sufficient certificate, not a necessary condition.
The parameters and the local weight function are fixed before N tends to infinity.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

theorem riemannHypothesis_iff_eventually_localProduct_of_log_reference
    (w : Nat.Primes -> Real) (nu z kappa C : Real)
    (hw : forall p, 0 <= w p) (hnu : 0 < nu) (hz : 0 < z) (hC : 0 <= C)
    (hTail : Filter.Eventually (fun N : Nat =>
      abs (kappa - (primeProfilePrefixSet N).sum (fun p =>
        Real.log (1 + w p * z) - nu * z * Real.log (1 + primeProfileWeight (p : Nat)))) <=
        C / N) atTop) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      Real.exp (nu * z * Real.eulerMascheroniConstant + kappa) *
        (Real.log (Chebyshev.theta (N : Real))) ^ (nu * z) <
          (primeProfilePrefixSet N).prod (fun p => 1 + w p * z)) atTop := by
  let E : Nat -> Real := fun N =>
    nu * z * (Real.eulerMascheroniConstant +
      Real.log (Real.log (Chebyshev.theta (N : Real)))) + kappa -
      (primeProfilePrefixSet N).sum (fun p => Real.log (1 + w p * z))
  have hTheta := tendsto_primeProfile_theta_atTop.eventually_gt_atTop (1 : Real)
  have hError : Filter.Eventually (fun N : Nat =>
      abs (E N - (nu * z) * nicolasLogMertensOscillation (N : Real)) <=
        (nu * z) / 2 * abs (nicolasLogMertensOscillation (N : Real)) + C / N) atTop := by
    filter_upwards [hTail, hTheta] with N hT hThetaN
    have hEq : E N - (nu * z) * nicolasLogMertensOscillation (N : Real) =
        kappa - (primeProfilePrefixSet N).sum (fun p =>
          Real.log (1 + w p * z) - nu * z * Real.log (1 + primeProfileWeight (p : Nat))) := by
      rw [nicolasLog_nat_eq_primeProfile_clock_difference N hThetaN]
      dsimp [E]
      rw [Finset.sum_sub_distrib, <- Finset.mul_sum]
      ring
    rw [hEq]
    have hExtra : 0 <= (nu * z) / 2 * abs (nicolasLogMertensOscillation (N : Real)) := by positivity
    linarith only [hT, hExtra]
  rw [riemannHypothesis_iff_eventually_familyError_neg E (nu * z) C (mul_pos hnu hz) hC hError]
  apply Filter.eventually_congr
  filter_upwards [hTheta] with N hThetaN
  let P := (primeProfilePrefixSet N).prod (fun p => 1 + w p * z)
  let Q := Real.exp (nu * z * Real.eulerMascheroniConstant + kappa) *
    (Real.log (Chebyshev.theta (N : Real))) ^ (nu * z)
  have hP : 0 < P := Finset.prod_pos (fun p _ => by have h := mul_nonneg (hw p) hz.le; linarith)
  have hQ : 0 < Q := mul_pos (Real.exp_pos _)
    (Real.rpow_pos_of_pos (Real.log_pos hThetaN) _)
  have hLog : Real.log (Q / P) = E N := by
    rw [Real.log_div hQ.ne' hP.ne']
    dsimp [Q, P, E]
    rw [Real.log_mul (Real.exp_pos _).ne'
      (Real.rpow_pos_of_pos (Real.log_pos hThetaN) _).ne', Real.log_exp,
      Real.log_rpow (Real.log_pos hThetaN),
      Real.log_prod (fun p _ =>
        (show 0 < 1 + w p * z by have h := mul_nonneg (hw p) hz.le; linarith).ne')]
    ring
  change E N < 0 <-> Q < P
  rw [<- hLog]
  constructor
  . intro h
    have he := Real.exp_lt_exp.mpr h
    rw [Real.exp_log (div_pos hQ hP), Real.exp_zero] at he
    exact (div_lt_one hP).mp he
  . intro h
    have hl := Real.log_lt_log (div_pos hQ hP) ((div_lt_one hP).mpr h)
    simpa only [Real.log_one] using hl

end PrimeFactorOscillations
