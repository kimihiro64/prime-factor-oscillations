/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGammaShift

/-! # Complete shifted Gamma tails with explicit padded endpoints

The original outside interval is retained. A small nonnegative shift
maps it into the two actual Gamma(N+1,1) tails. Large shifts are bounded
by the full shifted integral, for the subsequent Gaussian MGF consumer.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory

theorem gammaShiftKernel_plain_integrable (n : Nat) (w : Real) (hw : 0 <= w) :
    Integrable (fun t : Real => Real.exp (-t) * (t + w) ^ n) gammaHalfLine := by
  simpa only [mul_one] using
    gammaShiftKernel_integrable n w (fun _ => (1 : Real)) hw
      (by simpa only [mul_one] using gammaKernel_integrable n)

theorem gammaShiftKernel_indicator_integrable (n : Nat) (w : Real) (E : Set Real)
    (hw : 0 <= w) (hE : MeasurableSet E) :
    Integrable (fun t : Real => Real.exp (-t) * (t + w) ^ n *
      Set.indicator E (fun _ => (1 : Real)) (t + w)) gammaHalfLine := by
  apply gammaShiftKernel_integrable n w _ hw
  have hFun :
      (fun t : Real => Real.exp (-t) * t ^ n *
        Set.indicator E (fun _ => (1 : Real)) t) =
      Set.indicator E (fun t : Real => Real.exp (-t) * t ^ n) := by
    funext t
    by_cases ht : Membership.mem E t <;> simp [Set.indicator, ht]
  rw [hFun]
  exact (gammaKernel_integrable n).indicator hE

def gammaShiftOutsideAverage (n : Nat) (w ell r : Real) : Real :=
  Inv.inv (n.factorial : Real) *
    MeasureTheory.integral gammaHalfLine
      (Set.indicator (Set.compl (Set.Icc ell r))
        (fun t : Real => Real.exp (-t) * (t + w) ^ n))

theorem gammaShiftOutsideAverage_le_full (n : Nat) (w ell r : Real) (hw : 0 <= w) :
    gammaShiftOutsideAverage n w ell r <= Real.exp w := by
  have hInt := gammaShiftKernel_plain_integrable n w hw
  have hOut := hInt.indicator (s := Set.compl (Set.Icc ell r))
    (measurableSet_Icc.compl)
  have hIntegral :
      MeasureTheory.integral gammaHalfLine
          (Set.indicator (Set.compl (Set.Icc ell r))
            (fun t : Real => Real.exp (-t) * (t + w) ^ n)) <=
        MeasureTheory.integral gammaHalfLine
          (fun t : Real => Real.exp (-t) * (t + w) ^ n) := by
    apply integral_mono_ae hOut hInt
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    have hKernel : 0 <= Real.exp (-t) * (t + w) ^ n :=
      mul_nonneg (Real.exp_pos _).le (pow_nonneg (add_nonneg (show 0 <= t from le_of_lt ht) hw) _)
    by_cases h : Membership.mem (Set.compl (Set.Icc ell r)) t
    case pos => simp [Set.indicator, h]
    case neg => simpa [Set.indicator, h] using hKernel
  apply le_trans (show gammaShiftOutsideAverage n w ell r <=
      gammaShiftAverage n w (fun _ => (1 : Real)) from ?_)
    (gammaShiftAverage_one_le n w hw)
  unfold gammaShiftOutsideAverage gammaShiftAverage
  simp only [mul_one]
  exact mul_le_mul_of_nonneg_left hIntegral (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem shiftedOutside_indicator_le (w ell r low high t : Real)
    (hw : 0 <= w) (hLow : ell + w <= low) (hHigh : high <= r) :
    Set.indicator (Set.compl (Set.Icc ell r)) (fun _ => (1 : Real)) t <=
      Set.indicator (Set.Iic low) (fun _ => (1 : Real)) (t + w) +
        Set.indicator (Set.Ici high) (fun _ => (1 : Real)) (t + w) := by
  by_cases hOut : Membership.mem (Set.compl (Set.Icc ell r)) t
  case pos =>
    have hTail : Or (t + w <= low) (high <= t + w) := by
      change Not (And (ell <= t) (t <= r)) at hOut
      by_cases ht : t < ell
      case pos => exact Or.inl (by linarith)
      case neg =>
        have hr : r < t := by
          by_contra h
          exact hOut (And.intro (le_of_not_gt ht) (le_of_not_gt h))
        exact Or.inr (by linarith)
    by_cases hLo : t + w <= low
    case pos =>
      by_cases hHi : high <= t + w <;> simp [Set.indicator, hOut, hLo, hHi]
    case neg =>
      have hHi : high <= t + w := hTail.resolve_left hLo
      simp [Set.indicator, hOut, hLo, hHi]
  case neg =>
    by_cases hLo : t + w <= low <;>
      by_cases hHi : high <= t + w <;> simp [Set.indicator, hOut, hLo, hHi]

theorem gammaShiftOutsideAverage_central (n : Nat) (w ell r x : Real)
    (hw : 0 <= w) (hx0 : 0 <= x) (hx1 : x < 1)
    (hLow : ell + w <= ((n : Real) + 1) * (1 - x))
    (hHigh : ((n : Real) + 1) * (1 + x) <= r) :
    gammaShiftOutsideAverage n w ell r <=
      2 * Real.exp w * Real.exp (-((n : Real) + 1) * x ^ 2 / 9) := by
  let lo := Set.indicator (Set.Iic (((n : Real) + 1) * (1 - x)))
    (fun _ => (1 : Real))
  let hi := Set.indicator (Set.Ici (((n : Real) + 1) * (1 + x)))
    (fun _ => (1 : Real))
  have hIntLo := gammaShiftKernel_indicator_integrable n w
    (Set.Iic (((n : Real) + 1) * (1 - x))) hw measurableSet_Iic
  have hIntHi := gammaShiftKernel_indicator_integrable n w
    (Set.Ici (((n : Real) + 1) * (1 + x))) hw measurableSet_Ici
  have hOut := (gammaShiftKernel_plain_integrable n w hw).indicator
    (s := Set.compl (Set.Icc ell r)) (measurableSet_Icc.compl)
  have hDom : Filter.Eventually (fun t : Real =>
      Set.indicator (Set.compl (Set.Icc ell r))
          (fun u : Real => Real.exp (-u) * (u + w) ^ n) t <=
        Real.exp (-t) * (t + w) ^ n * lo (t + w) +
          Real.exp (-t) * (t + w) ^ n * hi (t + w)) (ae gammaHalfLine) := by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    have hKernel : 0 <= Real.exp (-t) * (t + w) ^ n :=
      mul_nonneg (Real.exp_pos _).le (pow_nonneg (add_nonneg (show 0 <= t from le_of_lt ht) hw) _)
    have h := mul_le_mul_of_nonneg_left
      (shiftedOutside_indicator_le w ell r _ _ t hw hLow hHigh) hKernel
    have hLeft : Set.indicator (Set.compl (Set.Icc ell r))
        (fun u : Real => Real.exp (-u) * (u + w) ^ n) t =
      (Real.exp (-t) * (t + w) ^ n) *
        Set.indicator (Set.compl (Set.Icc ell r)) (fun _ => (1 : Real)) t := by
      by_cases hE : Membership.mem (Set.compl (Set.Icc ell r)) t <;>
        simp [Set.indicator, hE]
    rw [hLeft]
    rw [mul_add] at h
    exact h
  have hIntegral := integral_mono_ae hOut (hIntLo.add hIntHi) hDom
  have hSum : gammaShiftOutsideAverage n w ell r <=
      gammaShiftAverage n w lo + gammaShiftAverage n w hi := by
    unfold gammaShiftOutsideAverage gammaShiftAverage
    change MeasureTheory.integral gammaHalfLine
        (Set.indicator (Set.compl (Set.Icc ell r))
          (fun t : Real => Real.exp (-t) * (t + w) ^ n)) <=
      MeasureTheory.integral gammaHalfLine (fun t =>
        Real.exp (-t) * (t + w) ^ n * lo (t + w) +
          Real.exp (-t) * (t + w) ^ n * hi (t + w)) at hIntegral
    rw [integral_add hIntLo hIntHi] at hIntegral
    calc
      _ <= Inv.inv (n.factorial : Real) *
          (MeasureTheory.integral gammaHalfLine (fun t =>
            Real.exp (-t) * (t + w) ^ n * lo (t + w)) +
          MeasureTheory.integral gammaHalfLine (fun t =>
            Real.exp (-t) * (t + w) ^ n * hi (t + w))) :=
        mul_le_mul_of_nonneg_left hIntegral (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = _ := by ring
  have hLo := gammaShiftAverage_lower_central n w x hw hx0 hx1
  have hHi := gammaShiftAverage_upper_central n w x hw hx0 hx1.le
  have hExp : Real.exp (-((n : Real) + 1) * x ^ 2 / 4) <=
      Real.exp (-((n : Real) + 1) * x ^ 2 / 9) := by
    apply Real.exp_le_exp.mpr
    have h0 := mul_nonneg (show (0 : Real) <= (n : Real) + 1 by
      exact add_nonneg (Nat.cast_nonneg _) zero_le_one) (sq_nonneg x)
    nlinarith
  calc
    _ <= Real.exp w * Real.exp (-((n : Real) + 1) * x ^ 2 / 4) +
        Real.exp w * Real.exp (-((n : Real) + 1) * x ^ 2 / 9) :=
      le_trans hSum (add_le_add hLo hHi)
    _ <= Real.exp w * Real.exp (-((n : Real) + 1) * x ^ 2 / 9) +
        Real.exp w * Real.exp (-((n : Real) + 1) * x ^ 2 / 9) :=
      add_le_add (mul_le_mul_of_nonneg_left hExp (Real.exp_pos _).le) le_rfl
    _ = _ := by ring

theorem gammaShiftOutside_endpoints (n : Nat) (w delta : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hN : 8 <= (n : Real) * delta) (hw : w <= delta * (n : Real) / 16) :
    And ((n : Real) / (1 + delta / 4) + w <=
        ((n : Real) + 1) * (1 - delta / 16))
      (((n : Real) + 1) * (1 + delta / 16) <=
        (n : Real) / (1 - delta / 4)) := by
  have hn0 : 0 <= (n : Real) := Nat.cast_nonneg n
  have hp : 0 < 1 + delta / 4 := by linarith
  have hm : 0 < 1 - delta / 4 := by linarith
  have hPlus : (n : Real) / (1 + delta / 4) <=
      (n : Real) * (1 - delta / 8) := by
    by_contra h
    have hStrict := mul_lt_mul_of_pos_right (lt_of_not_ge h) hp
    have hCancel : ((n : Real) / (1 + delta / 4)) * (1 + delta / 4) = n := by
      field_simp
    rw [hCancel] at hStrict
    have hProd : 1 <= (1 - delta / 8) * (1 + delta / 4) := by nlinarith
    have hBound := mul_le_mul_of_nonneg_left hProd hn0
    nlinarith
  have hMinus : (n : Real) * (1 + delta / 4) <=
      (n : Real) / (1 - delta / 4) := by
    by_contra h
    have hStrict := mul_lt_mul_of_pos_right (lt_of_not_ge h) hm
    have hCancel : ((n : Real) / (1 - delta / 4)) * (1 - delta / 4) = n := by
      have hDen : Not (4 - delta = 0) := by linarith
      field_simp [hDen]
    rw [hCancel] at hStrict
    have hProd : (1 + delta / 4) * (1 - delta / 4) <= 1 := by nlinarith
    have hBound := mul_le_mul_of_nonneg_left hProd hn0
    nlinarith
  exact And.intro (by nlinarith) (by nlinarith)

theorem gammaShiftOutsideAverage_delta (n : Nat) (w delta : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hN : 8 <= (n : Real) * delta) (hw0 : 0 <= w)
    (hw1 : w <= delta * (n : Real) / 16) :
    gammaShiftOutsideAverage n w
        ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)) <=
      2 * Real.exp w * Real.exp (-((n : Real) + 1) * delta ^ 2 / 2304) := by
  have hEnds := gammaShiftOutside_endpoints n w delta hDelta0 hDelta1 hN hw1
  have h := gammaShiftOutsideAverage_central n w
    ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4))
    (delta / 16) hw0 (by linarith) (by linarith) hEnds.1 hEnds.2
  have hExp : -((n : Real) + 1) * (delta / 16) ^ 2 / 9 =
      -((n : Real) + 1) * delta ^ 2 / 2304 := by ring
  simpa only [hExp] using h

end PrimeFactorOscillations
