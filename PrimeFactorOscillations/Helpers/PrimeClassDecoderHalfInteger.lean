/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Helpers.PrimeClassSamplingEuler

/-!
# Signed half-integer factors for the actual class Euler product

Every active numerator stays at least one half from zero. Its sign is
negative exactly at the prime labels p <= n+1. The late positive factors
retain a logarithmic lower bound before any infinite-product passage.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

theorem classEulerFactor_halfInteger
    (P : Set Nat) (p n : Nat) (hp : Nat.Prime p) (hP : Membership.mem P p) :
    classEulerFactor P p (((-(n : Real) - 1 / 2 : Real) : Complex)) =
      ((((p : Real) - (n : Real) - 3 / 2) / (p : Real) : Real) : Complex) := by
  have hweight : classPowerWeight P 1 p = 1 / (p : Real) := by
    simp [classPowerWeight, And.intro hp hP, Real.rpow_neg_one]
  rw [classEulerFactor, hweight]
  push_cast
  have hpC : Not ((p : Complex) = 0) := Nat.cast_ne_zero.mpr hp.ne_zero
  field_simp [hpC]
  ring

theorem halfInteger_numerator_gap (p n : Nat) :
    (1 / 2 : Real) <= abs ((p : Real) - (n : Real) - 3 / 2) := by
  by_cases hpn : p <= n + 1
  case pos =>
    have hpnR : (p : Real) <= (n : Real) + 1 := by exact_mod_cast hpn
    rw [abs_of_nonpos (by linarith : (p : Real) - (n : Real) - 3 / 2 <= 0)]
    linarith
  case neg =>
    have hnp : n + 2 <= p := by omega
    have hnpR : (n : Real) + 2 <= (p : Real) := by exact_mod_cast hnp
    rw [abs_of_nonneg (by linarith : 0 <= (p : Real) - (n : Real) - 3 / 2)]
    linarith

theorem halfInteger_factor_neg_iff
    (p n : Nat) (hp : 0 < p) :
    ((p : Real) - (n : Real) - 3 / 2) / (p : Real) < 0 <-> p <= n + 1 := by
  have hpR : (0 : Real) < (p : Real) := by exact_mod_cast hp
  constructor
  case mp =>
    intro hneg
    by_contra hn
    have hnp : n + 2 <= p := by omega
    have hnpR : (n : Real) + 2 <= (p : Real) := by exact_mod_cast hnp
    have hpos := div_pos (by linarith : 0 < (p : Real) - (n : Real) - 3 / 2) hpR
    linarith
  case mpr =>
    intro hpn
    have hpnR : (p : Real) <= (n : Real) + 1 := by exact_mod_cast hpn
    exact div_neg_of_neg_of_pos (by linarith) hpR

theorem halfInteger_factor_abs_ge
    (p n : Nat) (hp : 0 < p) :
    1 / (2 * (p : Real)) <= abs (((p : Real) - (n : Real) - 3 / 2) / (p : Real)) := by
  have hpR : (0 : Real) < (p : Real) := by exact_mod_cast hp
  rw [abs_div, abs_of_pos hpR]
  have h := div_le_div_of_nonneg_right (halfInteger_numerator_gap p n) hpR.le
  have hid : (1 / 2 : Real) / (p : Real) = 1 / (2 * (p : Real)) := by ring
  rwa [hid] at h

theorem earlyHalfInteger_factor_abs_ge
    (R p n : Nat) (hR : 1 <= R) (hp : 0 < p) (hpR : p <= 4 * R + 2) :
    1 / (12 * (R : Real)) <= abs (((p : Real) - (n : Real) - 3 / 2) / (p : Real)) := by
  have hRR : (1 : Real) <= (R : Real) := by exact_mod_cast hR
  have hpRreal : (p : Real) <= 4 * (R : Real) + 2 := by exact_mod_cast hpR
  have hpReal : (0 : Real) < (p : Real) := by exact_mod_cast hp
  have hden : 2 * (p : Real) <= 12 * (R : Real) := by linarith
  exact (div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1)
    (by positivity : (0 : Real) < 2 * (p : Real)) hden).trans
      (halfInteger_factor_abs_ge p n hp)

theorem lateHalfInteger_ratio_bounds
    (R p n : Nat) (hR : 1 <= R) (hn : n <= R) (hpR : 4 * R + 2 < p) :
    And (0 <= ((n : Real) + 3 / 2) / (p : Real))
      (((n : Real) + 3 / 2) / (p : Real) < 1 / 2) := by
  have hp : 0 < p := by omega
  have hpReal : (0 : Real) < (p : Real) := by exact_mod_cast hp
  have hRR : (1 : Real) <= (R : Real) := by exact_mod_cast hR
  have hnR : (n : Real) <= (R : Real) := by exact_mod_cast hn
  have hpRreal : 4 * (R : Real) + 2 < (p : Real) := by exact_mod_cast hpR
  have hnum : 2 * ((n : Real) + 3 / 2) < (p : Real) := by linarith
  have h := div_lt_div_of_pos_right hnum hpReal
  have hid : 2 * ((n : Real) + 3 / 2) / (p : Real) =
      2 * (((n : Real) + 3 / 2) / (p : Real)) := by ring
  rw [hid, div_self (ne_of_gt hpReal)] at h
  exact And.intro (div_nonneg (by positivity) hpReal.le) (by linarith)

theorem log_one_sub_ge_neg_two_mul
    (t : Real) (ht : 0 <= t) (ht2 : t <= 1 / 2) :
    -2 * t <= Real.log (1 - t) := by
  have hpos : 0 < 1 - t := by linarith
  have hlog := Real.log_le_sub_one_of_pos (one_div_pos.mpr hpos)
  rw [Real.log_div (by norm_num : Not ((1 : Real) = 0)) (ne_of_gt hpos),
    Real.log_one, zero_sub] at hlog
  have hdiv := div_le_div_of_nonneg_left ht (by norm_num : (0 : Real) < 1 / 2)
    (by linarith : (1 / 2 : Real) <= 1 - t)
  have hid : 1 / (1 - t) - 1 = t / (1 - t) := by field_simp; ring
  rw [hid] at hlog
  have hhalf : t / (1 / 2 : Real) = 2 * t := by ring
  rw [hhalf] at hdiv
  linarith

end PrimeFactorOscillations.PrimeClassSampling
