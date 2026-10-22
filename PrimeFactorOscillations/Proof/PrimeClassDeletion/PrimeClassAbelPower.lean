/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassAbel

/-! # Quantitative Abel remainder bounds from an actual class-mass bound -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem primeClassAbel_intervalIntegrable_between (P : Set Nat) (a z : Real)
    (ha : 2 <= a) (haz : a <= z) :
    IntervalIntegrable (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume a z := by
  apply (primeClassAbel_intervalIntegrable P z (ha.trans haz)).mono_set
  intro t ht
  rw [Set.uIcc_of_le haz] at ht
  rw [Set.uIcc_of_le (ha.trans haz)]
  exact And.intro (ha.trans ht.1) ht.2

theorem primeClassAbel_integral_nonneg (P : Set Nat) (a z : Real)
    (ha : 2 <= a) (haz : a <= z) :
    0 <= intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
      a z MeasureTheory.volume := by
  apply intervalIntegral.integral_nonneg haz
  intro t ht
  exact div_nonneg (primeClassThetaReal_nonneg P t)
    (mul_nonneg (by linarith only [ha, ht.1]) (sq_nonneg _))

theorem primeClassAbel_power_pointwise (P : Set Nat) (b C a t : Real)
    (hC : 0 <= C) (ha : 2 <= a) (hat : a <= t)
    (hmass : primeClassThetaReal P t <= C * t ^ b) :
    primeClassThetaReal P t / (t * (Real.log t) ^ 2) <=
      (C / (Real.log a) ^ 2) * t ^ (b - 1) := by
  have ht0 : 0 < t := by linarith only [ha, hat]
  have hla : 0 < Real.log a := Real.log_pos (by linarith only [ha])
  have hlt : 0 < Real.log t := Real.log_pos (by linarith only [ha, hat])
  have hlogs := Real.log_le_log (by linarith only [ha]) hat
  have hlogsq : (Real.log a) ^ 2 <= (Real.log t) ^ 2 := by
    nlinarith only [hla, hlt, hlogs]
  have hpow : t ^ b / t = t ^ (b - 1) := by
    rw [Real.rpow_sub ht0, Real.rpow_one]
  have hN : 0 <= C * t ^ (b - 1) :=
    mul_nonneg hC (Real.rpow_pos_of_pos ht0 _).le
  calc
    primeClassThetaReal P t / (t * (Real.log t) ^ 2) <=
        (C * t ^ b) / (t * (Real.log t) ^ 2) :=
      div_le_div_of_nonneg_right hmass (mul_nonneg ht0.le (sq_nonneg _))
    _ = (C * t ^ (b - 1)) / (Real.log t) ^ 2 := by
      rw [<- hpow]
      field_simp
    _ <= (C * t ^ (b - 1)) / (Real.log a) ^ 2 :=
      div_le_div_of_nonneg_left hN (sq_pos_of_pos hla) hlogsq
    _ = (C / (Real.log a) ^ 2) * t ^ (b - 1) := by ring

theorem primeClassAbel_power_interval_bound (P : Set Nat) (b C a z : Real)
    (hb : 0 < b) (hC : 0 <= C) (ha : 2 <= a) (haz : a <= z)
    (hmass : forall t : Real, a <= t -> t <= z -> primeClassThetaReal P t <= C * t ^ b) :
    intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
        a z MeasureTheory.volume <= C * z ^ b / (b * (Real.log a) ^ 2) := by
  have hpower : IntervalIntegrable (fun t : Real => t ^ (b - 1))
      MeasureTheory.volume a z :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith only [hb])
  have hmajorant := intervalIntegral.integral_mono_on haz
    (primeClassAbel_intervalIntegrable_between P a z ha haz)
    (hpower.const_mul (C / (Real.log a) ^ 2)) (by
      intro t ht
      exact primeClassAbel_power_pointwise P b C a t hC ha ht.1 (hmass t ht.1 ht.2))
  rw [intervalIntegral.integral_const_mul] at hmajorant
  have hintegral : intervalIntegral (fun t : Real => t ^ (b - 1)) a z MeasureTheory.volume =
      (z ^ b - a ^ b) / b := by
    rw [integral_rpow (Or.inl (by linarith only [hb])), show b - 1 + 1 = b by ring]
  rw [hintegral] at hmajorant
  have hcoef : 0 <= C / (Real.log a) ^ 2 := div_nonneg hC (sq_nonneg _)
  have hpow : 0 <= a ^ b := Real.rpow_nonneg (by linarith only [ha]) b
  have hupper := div_le_div_of_nonneg_right (sub_le_self (z ^ b) hpow) hb.le
  have hproduct := mul_le_mul_of_nonneg_left hupper hcoef
  calc
    _ <= (C / (Real.log a) ^ 2) * ((z ^ b - a ^ b) / b) := hmajorant
    _ <= (C / (Real.log a) ^ 2) * (z ^ b / b) := hproduct
    _ = C * z ^ b / (b * (Real.log a) ^ 2) := by ring

theorem primeClassAbel_two_range_bound (P : Set Nat) (b C Y x : Real)
    (hb : 0 < b) (hC : 0 <= C) (hY : 2 <= Y) (hYx : Y <= x)
    (hmass : forall t : Real, 2 <= t -> primeClassThetaReal P t <= C * t ^ b) :
    intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
        2 x MeasureTheory.volume <=
      C * Y ^ b / (b * (Real.log 2) ^ 2) + C * x ^ b / (b * (Real.log Y) ^ 2) := by
  have hlow := primeClassAbel_power_interval_bound P b C 2 Y hb hC (le_refl _) hY
    (fun t ht _ => hmass t ht)
  have hhigh := primeClassAbel_power_interval_bound P b C Y x hb hC hY hYx
    (fun t ht _ => hmass t (hY.trans ht))
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (primeClassAbel_intervalIntegrable P Y hY)
    (primeClassAbel_intervalIntegrable_between P Y x hY hYx)
  linarith only [hlow, hhigh, hadd]

end PrimeFactorOscillations.PrimeClassDeletion
