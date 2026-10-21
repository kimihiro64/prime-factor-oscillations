/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Helpers.PrimeClassCountProfileLaw

/-!
# Fractional-order growth of a prime-class Euler profile

The summable p^(-sigma) mass controls the whole complex profile by an
exponential of r^sigma. This retains the decoder range h*sigma < 1.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

theorem log_one_add_le_rpow_div
    (y sigma : Real) (hy : 0 <= y) (hs : 0 < sigma) (hs1 : sigma <= 1) :
    Real.log (1 + y) <= y ^ sigma / sigma := by
  have hx : 0 < 1 + y := by linarith
  have hpow := Real.rpow_add_le_add_rpow (show (0 : Real) <= 1 by norm_num)
    hy hs.le hs1
  rw [Real.one_rpow] at hpow
  have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx sigma)
  rw [Real.log_rpow hx] at hlog
  have hmul : sigma * Real.log (1 + y) <= y ^ sigma := by linarith
  have hdiv := div_le_div_of_nonneg_right hmul hs.le
  have hcancel : sigma * Real.log (1 + y) / sigma = Real.log (1 + y) := by
    field_simp
  rwa [hcancel] at hdiv

theorem one_add_le_exp_rpow_div
    (y sigma : Real) (hy : 0 <= y) (hs : 0 < sigma) (hs1 : sigma <= 1) :
    1 + y <= Real.exp (y ^ sigma / sigma) := by
  have hx : 0 < 1 + y := by linarith
  have h := Real.exp_le_exp.mpr (log_one_add_le_rpow_div y sigma hy hs hs1)
  rwa [Real.exp_log hx] at h

theorem classPowerWeight_one_le_one (P : Set Nat) (p : Nat) :
    classPowerWeight P 1 p <= 1 := by
  classical
  unfold classPowerWeight
  split_ifs with hp
  case pos =>
    have hbase : (1 : Real) <= (p : Real) := by exact_mod_cast hp.1.one_lt.le
    calc
      _ <= (p : Real) ^ (0 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
      _ = 1 := Real.rpow_zero _
  case neg => norm_num

theorem classPowerWeight_one_rpow
    (P : Set Nat) (p : Nat) (sigma : Real) (hs : 0 < sigma) :
    (classPowerWeight P 1 p) ^ sigma = classPowerWeight P sigma p := by
  classical
  unfold classPowerWeight
  split_ifs with hp
  case pos =>
    rw [<- Real.rpow_mul (show (0 : Real) <= (p : Real) by positivity)]
    congr 1
    ring
  case neg => exact Real.zero_rpow (ne_of_gt hs)

theorem norm_classEulerFactor_le_one_add
    (P : Set Nat) (p : Nat) (z : Complex) (r : Real) (hz : norm z <= r) :
    norm (classEulerFactor P p z) <= 1 + classPowerWeight P 1 p * r := by
  let q := classPowerWeight P 1 p
  have hq : 0 <= q := classPowerWeight_nonneg P 1 p
  have hq1 : q <= 1 := classPowerWeight_one_le_one P p
  have hid : classEulerFactor P p z = ((1 - q : Real) : Complex) + (q : Complex) * z := by
    simp only [classEulerFactor, Complex.ofReal_sub, Complex.ofReal_one, q]
    ring
  calc
    _ <= norm (((1 - q : Real) : Complex)) + norm ((q : Complex) * z) := by
      rw [hid]
      exact norm_add_le _ _
    _ = 1 - q + q * norm z := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hq, abs_of_nonneg (sub_nonneg.mpr hq1)]
    _ <= 1 + q * r := by nlinarith [mul_le_mul_of_nonneg_left hz hq]

theorem norm_classEulerFactor_le_exp_rpow
    (P : Set Nat) (p : Nat) (z : Complex) (r sigma : Real)
    (hr : 0 <= r) (hz : norm z <= r) (hs : 0 < sigma) (hs1 : sigma <= 1) :
    norm (classEulerFactor P p z) <=
      Real.exp (classPowerWeight P sigma p * r ^ sigma / sigma) := by
  calc
    _ <= 1 + classPowerWeight P 1 p * r :=
      norm_classEulerFactor_le_one_add P p z r hz
    _ <= Real.exp ((classPowerWeight P 1 p * r) ^ sigma / sigma) :=
      one_add_le_exp_rpow_div _ sigma
        (mul_nonneg (classPowerWeight_nonneg P 1 p) hr) hs hs1
    _ = _ := by
      rw [Real.mul_rpow (classPowerWeight_nonneg P 1 p) hr,
        classPowerWeight_one_rpow P p sigma hs]

theorem norm_finiteEulerProduct_le_exp_rpow
    (P : Set Nat) (s : Finset Nat) (z : Complex) (r sigma : Real)
    (hr : 0 <= r) (hz : norm z <= r) (hs : 0 < sigma) (hs1 : sigma <= 1) :
    norm (s.prod (fun p => classEulerFactor P p z)) <=
      Real.exp (s.sum (fun p => classPowerWeight P sigma p * r ^ sigma / sigma)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    simp only [Finset.prod_insert hp, Finset.sum_insert hp, norm_mul, Real.exp_add]
    exact mul_le_mul (norm_classEulerFactor_le_exp_rpow P p z r sigma hr hz hs hs1)
      ih (norm_nonneg _) (Real.exp_nonneg _)

theorem norm_classEulerProfile_le_exp_rpow
    (P : Set Nat) (sigma r : Real) (hs : 0 < sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) (hr : 0 <= r)
    (z : Complex) (hz : norm z <= r) :
    norm (classEulerProfile P z) <=
      Real.exp ((tsum (classPowerWeight P sigma)) * r ^ sigma / sigma) := by
  have hlimit := (finiteReference_euler_eval_tendsto P
    (classPowerWeight_one_summable P sigma hs1 hsum) z).norm
  apply le_of_tendsto hlimit
  apply Filter.Eventually.of_forall
  intro Y
  rw [finiteReference_euler_eval]
  calc
    _ <= Real.exp ((primeClassPrefix P Y).sum
        (fun p => classPowerWeight P sigma p * r ^ sigma / sigma)) :=
      norm_finiteEulerProduct_le_exp_rpow P _ z r sigma hr hz hs hs1
    _ <= _ := by
      apply Real.exp_le_exp.mpr
      rw [<- Finset.sum_div, <- Finset.sum_mul]
      apply div_le_div_of_nonneg_right _ hs.le
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr sigma)
      exact hsum.sum_le_tsum _ (fun p _ => classPowerWeight_nonneg P sigma p)

end PrimeFactorOscillations.PrimeClassSampling
