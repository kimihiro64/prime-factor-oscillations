/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.FamilyNicolasTransfer
import PrimeFactorOscillations.Helpers.QuadraticPrimeLog

/-!
# General family RH product criteria

Every fixed positive tilt and every nonnegative quadratic local perturbation
has the same RH signal, with its own exact convergent profile constant.
Both strict and non-strict criteria follow, with inclusive integer cutoffs.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open Filter Robin1984

noncomputable def logError (law : QuadraticPrimeLaw) (N : Nat) (z : Real) : Real :=
  law.nu * z * (Real.eulerMascheroniConstant +
    Real.log (Real.log (Chebyshev.theta (N : Real)))) + law.logProfile z -
      (primeProfilePrefixSet N).sum (fun p => Real.log (1 + law.weight p * z))

theorem logError_eq_signal_add_tail (law : QuadraticPrimeLaw) (N : Nat) (z : Real)
    (hTheta : 1 < Chebyshev.theta (N : Real)) :
    law.logError N z = law.nu * z * nicolasLogMertensOscillation (N : Real) +
      (law.logProfile z - (primeProfilePrefixSet N).sum (law.logFactor z)) := by
  rw [nicolasLog_nat_eq_primeProfile_clock_difference N hTheta]
  unfold logError logFactor
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum]
  ring

theorem logError_bound (law : QuadraticPrimeLaw) (N : Nat) (hN : 1 <= N)
    (z : Real) (hz : 0 <= z) (hTheta : 1 < Chebyshev.theta (N : Real)) :
    abs (law.logError N z - law.nu * z * nicolasLogMertensOscillation (N : Real)) <=
      2 * law.logTailConstant z / N := by
  rw [law.logError_eq_signal_add_tail N z hTheta, add_sub_cancel_left]
  exact law.logProfile_tail_bound N hN z hz

theorem riemannHypothesis_iff_eventually_logError_le
    (law : QuadraticPrimeLaw) (z A : Real) (hz : 0 < z) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat => law.logError N z <= A / N) atTop := by
  apply riemannHypothesis_iff_eventually_familyError_le
    (fun N => law.logError N z) (law.nu * z) (2 * law.logTailConstant z) A
    (mul_pos law.nu_pos hz) (mul_nonneg (by norm_num) (law.logTailConstant_nonneg z hz.le))
  filter_upwards [eventually_ge_atTop (1 : Nat),
    tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1] with N hN hTheta
  have hb := law.logError_bound N hN z hz.le hTheta
  have hExtra : 0 <= law.nu * z / 2 * abs (nicolasLogMertensOscillation (N : Real)) := by
    have hNu := law.nu_pos
    positivity
  linarith only [hb, hExtra]

theorem riemannHypothesis_iff_eventually_logError_neg
    (law : QuadraticPrimeLaw) (z : Real) (hz : 0 < z) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat => law.logError N z < 0) atTop := by
  constructor
  . intro hRH
    have h := (law.riemannHypothesis_iff_eventually_logError_le z (-1) hz).mp hRH
    filter_upwards [h, eventually_ge_atTop (1 : Nat)] with N hN hOne
    have hn : (0 : Real) < N := by exact_mod_cast hOne
    exact hN.trans_lt (div_neg_of_neg_of_pos (by norm_num) hn)
  . intro h
    apply (law.riemannHypothesis_iff_eventually_logError_le z 0 hz).mpr
    filter_upwards [h] with N hN
    simpa only [zero_div] using hN.le

noncomputable def referenceConstant (law : QuadraticPrimeLaw) (z : Real) : Real :=
  Real.exp (law.nu * z * Real.eulerMascheroniConstant + law.logProfile z)

theorem referenceConstant_pos (law : QuadraticPrimeLaw) (z : Real) :
    0 < law.referenceConstant z := Real.exp_pos _

theorem logError_eq_log_reference_div_product (law : QuadraticPrimeLaw)
    (N : Nat) (z : Real) (hz : 0 <= z) (hTheta : 1 < Chebyshev.theta (N : Real)) :
    law.logError N z = Real.log (law.referenceConstant z *
      (Real.log (Chebyshev.theta (N : Real))) ^ (law.nu * z) /
        law.prefixProduct N z) := by
  have hPower : 0 < (Real.log (Chebyshev.theta (N : Real))) ^ (law.nu * z) :=
    Real.rpow_pos_of_pos (Real.log_pos hTheta) _
  rw [Real.log_div (mul_pos (law.referenceConstant_pos z) hPower).ne'
    (law.prefixProduct_pos N z hz).ne',
    Real.log_mul (law.referenceConstant_pos z).ne' hPower.ne',
    Real.log_rpow (Real.log_pos hTheta)]
  unfold referenceConstant prefixProduct logError
  rw [Real.log_exp, Real.log_prod (fun p _ =>
    (show 0 < 1 + law.weight p * z by have h := mul_nonneg (law.weight_nonneg p) hz; linarith).ne')]
  ring

theorem logError_neg_iff_product (law : QuadraticPrimeLaw)
    (N : Nat) (z : Real) (hz : 0 <= z) (hTheta : 1 < Chebyshev.theta (N : Real)) :
    law.logError N z < 0 <-> law.referenceConstant z *
      (Real.log (Chebyshev.theta (N : Real))) ^ (law.nu * z) < law.prefixProduct N z := by
  have hPower : 0 < (Real.log (Chebyshev.theta (N : Real))) ^ (law.nu * z) :=
    Real.rpow_pos_of_pos (Real.log_pos hTheta) _
  have hNum := mul_pos (law.referenceConstant_pos z) hPower
  have hDen := law.prefixProduct_pos N z hz
  rw [law.logError_eq_log_reference_div_product N z hz hTheta]
  constructor
  . intro h
    have he := Real.exp_lt_exp.mpr h
    rw [Real.exp_log (div_pos hNum hDen), Real.exp_zero] at he
    exact (div_lt_one hDen).mp he
  . intro h
    have hq := (div_lt_one hDen).mpr h
    have hl := Real.log_lt_log (div_pos hNum hDen) hq
    simpa only [Real.log_one] using hl

theorem riemannHypothesis_iff_eventually_product
    (law : QuadraticPrimeLaw) (z : Real) (hz : 0 < z) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      law.referenceConstant z * (Real.log (Chebyshev.theta (N : Real))) ^ (law.nu * z) <
        law.prefixProduct N z) atTop := by
  rw [law.riemannHypothesis_iff_eventually_logError_neg z hz]
  apply Filter.eventually_congr
  filter_upwards [tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1] with N hN
  exact law.logError_neg_iff_product N z hz.le hN

end PrimeFactorOscillations.QuadraticPrimeLaw
