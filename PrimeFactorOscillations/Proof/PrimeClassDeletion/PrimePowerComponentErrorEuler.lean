/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentClassLimit

/-!
# Convergence of the complete prime-power error Euler product

The exact geometric denominators are retained. Its logarithmic series is
summable, and the actual prime-prefix products converge to its exponential.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

private theorem error_factor_pos (p : Nat) (hp : Nat.Prime p)
    (sigma : Real) (hs : 0 < sigma) :
    0 < (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma)) := by
  have hu := Real.rpow_nonneg (Nat.cast_nonneg p) (-sigma)
  have hv : (p : Real) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)
  exact div_pos (by linarith) (sub_pos.mpr hv)

private theorem error_factor_one_le (p : Nat) (hp : Nat.Prime p)
    (sigma : Real) (hs : 0 < sigma) :
    1 <= (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma)) := by
  have hu := Real.rpow_nonneg (Nat.cast_nonneg p) (-sigma)
  have hv : (p : Real) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)
  calc
    1 = (1 - (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma)) :=
      (div_self (ne_of_gt (sub_pos.mpr hv))).symm
    _ <= _ := div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr hv).le

noncomputable def classPrimePowerErrorLog (P : Set Nat) (sigma : Real) (p : Nat) : Real := by
  classical
  exact if And (Nat.Prime p) (Membership.mem P p) then
    Real.log ((1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma))) else 0

noncomputable def classPrimePowerErrorConstant (P : Set Nat) (sigma : Real) : Real :=
  Real.exp (tsum (classPrimePowerErrorLog P sigma))

theorem classPrimePowerErrorLog_nonneg
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma) (p : Nat) :
    0 <= classPrimePowerErrorLog P sigma p := by
  unfold classPrimePowerErrorLog
  split_ifs with h
  case pos => exact Real.log_nonneg (error_factor_one_le p h.1 sigma hs)
  case neg => exact le_refl 0

theorem classPrimePowerErrorLog_le
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma) (p : Nat) :
    classPrimePowerErrorLog P sigma p <=
      (2 / (1 - (2 : Real) ^ (-sigma))) * classPowerWeight P sigma p := by
  classical
  by_cases h : And (Nat.Prime p) (Membership.mem P p)
  case pos =>
    have hbudget : (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma)) <=
        Real.exp ((2 / (1 - (2 : Real) ^ (-sigma))) * (p : Real) ^ (-sigma)) := by
      simpa only [Finset.prod_singleton, Finset.sum_singleton] using
        primePowerEulerBudget_le_exp {p} (by
          intro q hq
          have heq : q = p := Finset.mem_singleton.mp hq
          rw [heq]
          exact h.1) sigma hs
    have hl := Real.log_le_log (error_factor_pos p h.1 sigma hs) hbudget
    rw [Real.log_exp] at hl
    simpa only [classPrimePowerErrorLog, classPowerWeight, ite_eq_left h] using hl
  case neg =>
    simp only [classPrimePowerErrorLog, classPowerWeight, ite_eq_right h, mul_zero, le_refl]

theorem classPrimePowerErrorLog_summable
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    Summable (classPrimePowerErrorLog P sigma) :=
  (hsum.mul_left (2 / (1 - (2 : Real) ^ (-sigma)))).of_nonneg_of_le
    (classPrimePowerErrorLog_nonneg P sigma hs)
    (classPrimePowerErrorLog_le P sigma hs)

theorem classPrimePowerErrorConstant_pos (P : Set Nat) (sigma : Real) :
    0 < classPrimePowerErrorConstant P sigma :=
  Real.exp_pos _

theorem classPrimePowerErrorConstant_le_uniform
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    classPrimePowerErrorConstant P sigma <=
      Real.exp ((2 / (1 - (2 : Real) ^ (-sigma))) *
        tsum (classPowerWeight P sigma)) := by
  have h := Summable.tsum_le_tsum (classPrimePowerErrorLog_le P sigma hs)
    (classPrimePowerErrorLog_summable P sigma hs hsum)
    (hsum.mul_left (2 / (1 - (2 : Real) ^ (-sigma))))
  rw [tsum_mul_left] at h
  exact Real.exp_le_exp.mpr h

theorem primePowerErrorEulerPrefix_eq_exp_sum
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma) (Y : Nat) :
    (primeClassPrefix P Y).prod (fun p =>
      (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma))) =
      Real.exp ((Finset.range (Y + 1)).sum (classPrimePowerErrorLog P sigma)) := by
  classical
  have hsub : forall p : Nat, Membership.mem (primeClassPrefix P Y) p ->
      Membership.mem (Finset.range (Y + 1)) p := by
    intro p hp
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2)
  have hsum :
      (primeClassPrefix P Y).sum (classPrimePowerErrorLog P sigma) =
        (Finset.range (Y + 1)).sum (classPrimePowerErrorLog P sigma) := by
    apply Finset.sum_subset hsub
    intro p hp hn
    by_cases h : And (Nat.Prime p) (Membership.mem P p)
    case pos =>
      have hm : Membership.mem (primeClassPrefix P Y) p :=
        Finset.mem_filter.mpr (And.intro
          (Finset.mem_Icc.mpr (And.intro h.1.two_le
            (Nat.le_of_lt_succ (Finset.mem_range.mp hp)))) h)
      exact False.elim (hn hm)
    case neg => simp only [classPrimePowerErrorLog, ite_eq_right h]
  rw [<- hsum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  have h := (Finset.mem_filter.mp hp).2
  rw [classPrimePowerErrorLog, ite_eq_left h, Real.exp_log (error_factor_pos p h.1 sigma hs)]

theorem primePowerErrorEulerPrefix_tendsto
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    Tendsto (fun Y : Nat => (primeClassPrefix P Y).prod (fun p =>
      (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma))))
      atTop (nhds (classPrimePowerErrorConstant P sigma)) := by
  have hsummable := classPrimePowerErrorLog_summable P sigma hs hsum
  have hsucc : Tendsto (fun Y : Nat => Y + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with Y hY
    exact hY.trans (Nat.le_succ Y)
  have h := hsummable.hasSum.tendsto_sum_nat.comp hsucc
  have heq : (fun Y : Nat => (primeClassPrefix P Y).prod (fun p =>
      (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma)))) =
        (fun Y : Nat => Real.exp
          ((Finset.range (Y + 1)).sum (classPrimePowerErrorLog P sigma))) :=
    funext (primePowerErrorEulerPrefix_eq_exp_sum P sigma hs)
  rw [heq]
  exact Real.continuous_exp.continuousAt.tendsto.comp h

end PrimeFactorOscillations.PrimeClassSampling
