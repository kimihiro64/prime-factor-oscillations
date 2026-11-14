/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Helpers.HamiltonianGammaMoments

/-! # Actual Gamma exponential moments and two-sided Chernoff estimates

The density is the normalized Euler integral on the positive half-line.
Its exponential moment is evaluated and its integrability proved. The
indicator bound is then applied to both upper and lower tails. No Gamma
probability law, moment assumption or concentration estimate is postulated.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def gammaDirectAverage (n : Nat) (f : Real -> Real) : Real :=
  Inv.inv (n.factorial : Real) *
    MeasureTheory.integral gammaHalfLine
      (fun t => Real.exp (-t) * t ^ n * f t)

theorem gammaInverseAverage_as_direct (n : Nat) (f : Real -> Real) :
    gammaInverseAverage n f =
      gammaDirectAverage n (fun t => f ((n : Real) / t)) := rfl

theorem gammaKernel_exponential_integral (n : Nat) (lambda : Real) (hLambda : lambda < 1) :
    MeasureTheory.integral gammaHalfLine
      (fun t : Real => Real.exp (-t) * t ^ n * Real.exp (lambda * t)) =
      (1 - lambda) ^ (-((n : Real) + 1)) * (n.factorial : Real) := by
  have hPos : -1 < (n : Real) := by
    linarith only [(show (0 : Real) <= (n : Real) from Nat.cast_nonneg n)]
  have hEuler := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : Real)) (q := (n : Real)) (b := 1 - lambda)
    zero_lt_one hPos (sub_pos.mpr hLambda)
  have hIntegral :
      MeasureTheory.integral gammaHalfLine
        (fun t : Real => t ^ n * Real.exp (-(1 - lambda) * t)) =
      (1 - lambda) ^ (-((n : Real) + 1)) * (n.factorial : Real) := by
    simpa only [gammaHalfLine, Real.rpow_one, Real.rpow_natCast, div_one,
      one_div_one, mul_one, Real.Gamma_nat_eq_factorial] using hEuler
  calc
    _ = MeasureTheory.integral gammaHalfLine
        (fun t : Real => t ^ n * Real.exp (-(1 - lambda) * t)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      calc
        _ = t ^ n * Real.exp (-t + lambda * t) := by
          rw [Real.exp_add]
          ring
        _ = _ := by
          congr 2
          ring
    _ = _ := hIntegral

theorem gammaKernel_exponential_integrable
    (n : Nat) (lambda : Real) (hLambda : lambda < 1) :
    MeasureTheory.Integrable
      (fun t : Real => Real.exp (-t) * t ^ n * Real.exp (lambda * t))
      gammaHalfLine := by
  have hFact : Not ((n.factorial : Real) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hNonzero :
      Not ((1 - lambda) ^ (-((n : Real) + 1)) * (n.factorial : Real) = 0) :=
    mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos (sub_pos.mpr hLambda) _)) hFact
  by_contra hNot
  have hZero := MeasureTheory.integral_undef hNot
  rw [gammaKernel_exponential_integral n lambda hLambda] at hZero
  exact hNonzero hZero

theorem gammaDirectAverage_exp (n : Nat) (lambda : Real) (hLambda : lambda < 1) :
    gammaDirectAverage n (fun t => Real.exp (lambda * t)) =
      (1 - lambda) ^ (-((n : Real) + 1)) := by
  unfold gammaDirectAverage
  rw [gammaKernel_exponential_integral n lambda hLambda]
  have hFact : Not ((n.factorial : Real) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hFact]

theorem gammaDirectAverage_indicator_le
    (n : Nat) (E : Set Real) (hE : MeasurableSet E) (lambda a : Real)
    (hLambda : lambda < 1)
    (hSide : forall t, Membership.mem E t -> 0 <= lambda * (t - a)) :
    gammaDirectAverage n (Set.indicator E (fun _ => (1 : Real))) <=
      Real.exp (-lambda * a) * (1 - lambda) ^ (-((n : Real) + 1)) := by
  have hIndicator :
      (fun t : Real => Real.exp (-t) * t ^ n *
        Set.indicator E (fun _ => (1 : Real)) t) =
      Set.indicator E (fun t : Real => Real.exp (-t) * t ^ n) := by
    funext t
    by_cases ht : Membership.mem E t
    case pos => simp [Set.indicator, ht]
    case neg => simp [Set.indicator, ht]
  have hLeft : MeasureTheory.Integrable
      (fun t : Real => Real.exp (-t) * t ^ n *
        Set.indicator E (fun _ => (1 : Real)) t) gammaHalfLine := by
    rw [hIndicator]
    exact (gammaKernel_integrable n).indicator hE
  have hRight : MeasureTheory.Integrable
      (fun t : Real => Real.exp (-lambda * a) *
        (Real.exp (-t) * t ^ n * Real.exp (lambda * t))) gammaHalfLine :=
    (gammaKernel_exponential_integrable n lambda hLambda).const_mul
      (Real.exp (-lambda * a))
  have hDom : Filter.Eventually
      (fun t : Real => Real.exp (-t) * t ^ n *
          Set.indicator E (fun _ => (1 : Real)) t <=
        Real.exp (-lambda * a) * (Real.exp (-t) * t ^ n * Real.exp (lambda * t)))
      (MeasureTheory.ae gammaHalfLine) := by
    apply (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    have hWeight : 0 <= Real.exp (-t) * t ^ n :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) (pow_nonneg (le_of_lt ht) n)
    by_cases htE : Membership.mem E t
    case pos =>
      have hTilt := Real.one_le_exp (hSide t htE)
      rw [show lambda * (t - a) = -lambda * a + lambda * t by ring,
        Real.exp_add] at hTilt
      simp only [Set.indicator_of_mem htE, mul_one]
      calc
        _ <= (Real.exp (-t) * t ^ n) *
            (Real.exp (-lambda * a) * Real.exp (lambda * t)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hTilt hWeight
        _ = _ := by ring
    case neg =>
      simp only [Set.indicator_of_notMem htE, mul_zero]
      exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (mul_nonneg hWeight (le_of_lt (Real.exp_pos _)))
  have hAverage :
      gammaDirectAverage n (Set.indicator E (fun _ => (1 : Real))) <=
        Real.exp (-lambda * a) *
          gammaDirectAverage n (fun t => Real.exp (lambda * t)) := by
    unfold gammaDirectAverage
    calc
      _ <= Inv.inv (n.factorial : Real) *
          MeasureTheory.integral gammaHalfLine
            (fun t : Real => Real.exp (-lambda * a) *
              (Real.exp (-t) * t ^ n * Real.exp (lambda * t))) :=
        mul_le_mul_of_nonneg_left (MeasureTheory.integral_mono_ae hLeft hRight hDom)
          (inv_nonneg.mpr (Nat.cast_nonneg n.factorial))
      _ = _ := by
        rw [MeasureTheory.integral_const_mul]
        ring
  rwa [gammaDirectAverage_exp n lambda hLambda] at hAverage

theorem gammaDirectAverage_upper_tail
    (n : Nat) (a lambda : Real) (hLambda0 : 0 <= lambda) (hLambda1 : lambda < 1) :
    gammaDirectAverage n (Set.indicator (Set.Ici a) (fun _ => (1 : Real))) <=
      Real.exp (-lambda * a) * (1 - lambda) ^ (-((n : Real) + 1)) := by
  apply gammaDirectAverage_indicator_le n (Set.Ici a) measurableSet_Ici
    lambda a hLambda1
  intro t ht
  exact mul_nonneg hLambda0 (sub_nonneg.mpr ht)

theorem gammaDirectAverage_lower_tail
    (n : Nat) (a lambda : Real) (hLambda0 : lambda <= 0) :
    gammaDirectAverage n (Set.indicator (Set.Iic a) (fun _ => (1 : Real))) <=
      Real.exp (-lambda * a) * (1 - lambda) ^ (-((n : Real) + 1)) := by
  apply gammaDirectAverage_indicator_le n (Set.Iic a) measurableSet_Iic
    lambda a (lt_of_le_of_lt hLambda0 zero_lt_one)
  intro t ht
  exact mul_nonneg_of_nonpos_of_nonpos hLambda0 (sub_nonpos.mpr ht)

end PrimeFactorOscillations
