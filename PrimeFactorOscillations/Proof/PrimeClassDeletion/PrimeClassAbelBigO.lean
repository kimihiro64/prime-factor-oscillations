/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassAbelLimit

/-! # An explicit uniform power-over-log-squared bound for the Abel remainder -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter

theorem primeClassAbel_power_log_square_bound (P : Set Nat) (b C : Real)
    (hb : 0 < b) (hC : 0 <= C)
    (hmass : forall t : Real, 2 <= t -> primeClassThetaReal P t <= C * t ^ b) :
    exists X : Real, And (4 <= X) (forall x : Real, X <= x ->
      And (0 <= intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
        2 x MeasureTheory.volume)
      (intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
          2 x MeasureTheory.volume <=
        (C / (b * (Real.log 2) ^ 2) + 4 * C / b) * x ^ b / (Real.log x) ^ 2)) := by
  have hbase := primeWave_log_div_power_tendsto (b / 4) (by linarith only [hb])
  have hlim := hbase.mul hbase
  simp only [mul_zero] at hlim
  choose X hX using Metric.tendsto_atTop.mp hlim 1 (by norm_num)
  refine Exists.intro (max 4 X) (And.intro (le_max_left 4 X) ?_)
  intro x hx
  have hx4 : 4 <= x := (le_max_left 4 X).trans hx
  have hx2 : 2 <= x := by linarith only [hx4]
  have hx0 : 0 < x := by linarith only [hx4]
  have hl : 0 < Real.log x := Real.log_pos (by linarith only [hx4])
  have hq : 0 < x ^ (b / 4) := Real.rpow_pos_of_pos hx0 (b / 4)
  have hh : 0 < x ^ (b / 2) := Real.rpow_pos_of_pos hx0 (b / 2)
  have hsmall : (Real.log x / x ^ (b / 4)) * (Real.log x / x ^ (b / 4)) <= 1 := by
    have h := hX x ((le_max_right 4 X).trans hx)
    have habs : abs ((Real.log x / x ^ (b / 4)) * (Real.log x / x ^ (b / 4))) < 1 := by
      simpa only [Real.dist_eq, sub_zero] using h
    exact ((le_abs_self _).trans_lt habs).le
  have hmul := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (x ^ (b / 4)))
  have hcancel : ((Real.log x / x ^ (b / 4)) * (Real.log x / x ^ (b / 4))) *
      (x ^ (b / 4)) ^ 2 = (Real.log x) ^ 2 := by field_simp
  rw [hcancel, one_mul] at hmul
  have hquarter : (x ^ (b / 4)) ^ 2 = x ^ (b / 2) := by
    rw [<- Real.rpow_two (x ^ (b / 4)), <- Real.rpow_mul hx0.le]
    congr 1
    ring
  rw [hquarter] at hmul
  have hpower : x ^ (b / 2) * x ^ (b / 2) = x ^ b := by
    rw [<- Real.rpow_add hx0]
    congr 1
    ring
  have hproduct := mul_le_mul_of_nonneg_right hmul hh.le
  rw [hpower] at hproduct
  have hquotient := div_le_div_of_nonneg_right hproduct (sq_nonneg (Real.log x))
  have hleft : ((Real.log x) ^ 2 * x ^ (b / 2)) / (Real.log x) ^ 2 = x ^ (b / 2) := by
    field_simp
  rw [hleft] at hquotient
  have hcoef : 0 <= C / (b * (Real.log 2) ^ 2) :=
    div_nonneg hC (mul_nonneg hb.le (sq_nonneg _))
  have hfirst := mul_le_mul_of_nonneg_left hquotient hcoef
  refine And.intro (primeClassAbel_integral_nonneg P 2 x (le_refl _) hx2) ?_
  calc
    _ <= (C / (b * (Real.log 2) ^ 2)) * x ^ (b / 2) +
        (4 * C / b) * x ^ b / (Real.log x) ^ 2 :=
      primeClassAbel_sqrt_bound P b C x hb hC hx4 hmass
    _ <= (C / (b * (Real.log 2) ^ 2)) * (x ^ b / (Real.log x) ^ 2) +
        (4 * C / b) * x ^ b / (Real.log x) ^ 2 := _root_.add_le_add hfirst (le_refl _)
    _ = _ := by ring

end PrimeFactorOscillations.PrimeClassDeletion
