/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.MeasureTheory.Group.Integral
import PrimeFactorOscillations.Helpers.HamiltonianGammaConcentration

/-! # Exact positive-half-line shifts for the collective Gamma remainder

The shift is kept in the actual Euler integral. It is used only for the
positive analytic remainder after every signed low-degree correction has
been retained. No local determinant factor is extended outside its window.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory

theorem realHalfLine_shift_indicator (f : Real -> Real) (w : Real) :
    Set.indicator (Set.Ioi (0 : Real)) (fun t => f (t + w)) =
      fun t => Set.indicator (Set.Ioi w) f (t + w) := by
  funext t
  by_cases ht : 0 < t
  case pos =>
    have hu : w < t + w := by linarith
    simp [Set.indicator, ht, hu]
  case neg =>
    have hu : Not (w < t + w) := by linarith
    simp [Set.indicator, ht, hu]

theorem realHalfLine_shift_integral (f : Real -> Real) (w : Real) :
    MeasureTheory.integral gammaHalfLine (fun t => f (t + w)) =
      MeasureTheory.integral (volume.restrict (Set.Ioi w)) f := by
  unfold gammaHalfLine
  calc
    _ = MeasureTheory.integral volume
        (Set.indicator (Set.Ioi (0 : Real)) (fun t => f (t + w))) :=
      (integral_indicator measurableSet_Ioi).symm
    _ = MeasureTheory.integral volume
        (fun t => Set.indicator (Set.Ioi w) f (t + w)) := by
      rw [realHalfLine_shift_indicator]
    _ = MeasureTheory.integral volume (Set.indicator (Set.Ioi w) f) :=
      integral_add_right_eq_self _ w
    _ = _ := integral_indicator measurableSet_Ioi

theorem realHalfLine_shift_integrable (f : Real -> Real) (w : Real)
    (hw : 0 <= w) (hf : Integrable f gammaHalfLine) :
    Integrable (fun t => f (t + w)) gammaHalfLine := by
  have hSub : Set.Subset (Set.Ioi w) (Set.Ioi (0 : Real)) := by
    intro t ht
    exact lt_of_le_of_lt hw ht
  have hOn : IntegrableOn f (Set.Ioi w) volume :=
    (show IntegrableOn f (Set.Ioi (0 : Real)) volume from hf).mono_set hSub
  have hInd : Integrable (Set.indicator (Set.Ioi w) f) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hOn
  have hTrans := hInd.comp_add_right w
  rw [<- realHalfLine_shift_indicator] at hTrans
  exact (integrable_indicator_iff measurableSet_Ioi).mp hTrans

theorem realHalfLine_shift_integral_le (f : Real -> Real) (w : Real)
    (hw : 0 <= w) (hf : Integrable f gammaHalfLine)
    (hNonneg : forall t, 0 < t -> 0 <= f t) :
    MeasureTheory.integral gammaHalfLine (fun t => f (t + w)) <=
      MeasureTheory.integral gammaHalfLine f := by
  have hSub : Set.Subset (Set.Ioi w) (Set.Ioi (0 : Real)) := by
    intro t ht
    exact lt_of_le_of_lt hw ht
  have hOn0 : IntegrableOn f (Set.Ioi (0 : Real)) volume := hf
  have hOnW : IntegrableOn f (Set.Ioi w) volume := hOn0.mono_set hSub
  have hInd0 : Integrable (Set.indicator (Set.Ioi (0 : Real)) f) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hOn0
  have hIndW : Integrable (Set.indicator (Set.Ioi w) f) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hOnW
  rw [realHalfLine_shift_integral]
  change MeasureTheory.integral (volume.restrict (Set.Ioi w)) f <=
    MeasureTheory.integral (volume.restrict (Set.Ioi (0 : Real))) f
  rw [<- integral_indicator measurableSet_Ioi, <- integral_indicator measurableSet_Ioi]
  apply integral_mono hIndW hInd0
  intro t
  by_cases ht : w < t
  case pos =>
    have h0 : 0 < t := lt_of_le_of_lt hw ht
    simp [Set.indicator, ht, h0]
  case neg =>
    by_cases h0 : 0 < t
    case pos => simpa [Set.indicator, ht, h0] using hNonneg t h0
    case neg => simp [Set.indicator, ht, h0]

def gammaShiftAverage (n : Nat) (w : Real) (f : Real -> Real) : Real :=
  Inv.inv (n.factorial : Real) *
    MeasureTheory.integral gammaHalfLine
      (fun t => Real.exp (-t) * (t + w) ^ n * f (t + w))

theorem gammaShiftKernel_factor (n : Nat) (w : Real) (f : Real -> Real) :
    (fun t : Real => Real.exp (-t) * (t + w) ^ n * f (t + w)) =
      fun t => Real.exp w *
        (Real.exp (-(t + w)) * (t + w) ^ n * f (t + w)) := by
  funext t
  have hExp : Real.exp (-t) = Real.exp w * Real.exp (-(t + w)) := by
    rw [<- Real.exp_add]
    congr 1
    ring
  rw [hExp]
  ring

theorem gammaShiftKernel_integrable (n : Nat) (w : Real) (f : Real -> Real)
    (hw : 0 <= w)
    (hf : Integrable (fun t : Real => Real.exp (-t) * t ^ n * f t) gammaHalfLine) :
    Integrable (fun t : Real => Real.exp (-t) * (t + w) ^ n * f (t + w))
      gammaHalfLine := by
  rw [gammaShiftKernel_factor]
  exact (realHalfLine_shift_integrable _ w hw hf).const_mul (Real.exp w)

theorem gammaShiftAverage_le (n : Nat) (w : Real) (f : Real -> Real)
    (hw : 0 <= w)
    (hf : Integrable (fun t : Real => Real.exp (-t) * t ^ n * f t) gammaHalfLine)
    (hNonneg : forall t, 0 < t -> 0 <= f t) :
    gammaShiftAverage n w f <= Real.exp w * gammaDirectAverage n f := by
  have hKernelNonneg : forall t : Real, 0 < t ->
      0 <= Real.exp (-t) * t ^ n * f t := by
    intro t ht
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le _))
      (hNonneg t ht)
  have hIntegral := realHalfLine_shift_integral_le
    (fun t : Real => Real.exp (-t) * t ^ n * f t) w hw hf hKernelNonneg
  unfold gammaShiftAverage gammaDirectAverage
  rw [gammaShiftKernel_factor, integral_const_mul]
  calc
    _ = Real.exp w * (Inv.inv (n.factorial : Real) *
        MeasureTheory.integral gammaHalfLine (fun t =>
          Real.exp (-(t + w)) * (t + w) ^ n * f (t + w))) := by ring
    _ <= _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hIntegral (inv_nonneg.mpr (Nat.cast_nonneg _)))
      (Real.exp_pos _).le

theorem gammaDirectAverage_one (n : Nat) :
    gammaDirectAverage n (fun _ => (1 : Real)) = 1 := by
  unfold gammaDirectAverage
  simp only [mul_one]
  rw [gammaKernel_integral]
  have hFact : Not ((n.factorial : Real) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hFact]

theorem gammaShiftAverage_one_le (n : Nat) (w : Real) (hw : 0 <= w) :
    gammaShiftAverage n w (fun _ => (1 : Real)) <= Real.exp w := by
  have hf : Integrable (fun t : Real => Real.exp (-t) * t ^ n * 1) gammaHalfLine := by
    simpa only [mul_one] using gammaKernel_integrable n
  have h := gammaShiftAverage_le n w (fun _ => (1 : Real)) hw hf
    (fun _ _ => zero_le_one)
  simpa only [gammaDirectAverage_one, mul_one] using h

theorem gammaShiftAverage_indicator_le (n : Nat) (w : Real) (E : Set Real)
    (hw : 0 <= w) (hE : MeasurableSet E) :
    gammaShiftAverage n w (Set.indicator E (fun _ => (1 : Real))) <=
      Real.exp w * gammaDirectAverage n (Set.indicator E (fun _ => (1 : Real))) := by
  have hFun :
      (fun t : Real => Real.exp (-t) * t ^ n *
        Set.indicator E (fun _ => (1 : Real)) t) =
      Set.indicator E (fun t : Real => Real.exp (-t) * t ^ n) := by
    funext t
    by_cases ht : Membership.mem E t <;> simp [Set.indicator, ht]
  apply gammaShiftAverage_le n w _ hw
  case hf =>
    rw [hFun]
    exact (gammaKernel_integrable n).indicator hE
  case hNonneg =>
    intro t ht
    by_cases h : Membership.mem E t <;> simp [Set.indicator, h]

theorem gammaShiftAverage_lower_central (n : Nat) (w x : Real)
    (hw : 0 <= w) (hx0 : 0 <= x) (hx1 : x < 1) :
    gammaShiftAverage n w
        (Set.indicator (Set.Iic (((n : Real) + 1) * (1 - x))) (fun _ => (1 : Real))) <=
      Real.exp w * Real.exp (-((n : Real) + 1) * x ^ 2 / 4) := by
  apply le_trans (gammaShiftAverage_indicator_le n w _ hw measurableSet_Iic)
  exact mul_le_mul_of_nonneg_left (gammaDirectAverage_lower_central n x hx0 hx1)
    (Real.exp_pos _).le

theorem gammaShiftAverage_upper_central (n : Nat) (w x : Real)
    (hw : 0 <= w) (hx0 : 0 <= x) (hx1 : x <= 1) :
    gammaShiftAverage n w
        (Set.indicator (Set.Ici (((n : Real) + 1) * (1 + x))) (fun _ => (1 : Real))) <=
      Real.exp w * Real.exp (-((n : Real) + 1) * x ^ 2 / 9) := by
  apply le_trans (gammaShiftAverage_indicator_le n w _ hw measurableSet_Ici)
  exact mul_le_mul_of_nonneg_left (gammaDirectAverage_upper_central n x hx0 hx1)
    (Real.exp_pos _).le

end PrimeFactorOscillations
