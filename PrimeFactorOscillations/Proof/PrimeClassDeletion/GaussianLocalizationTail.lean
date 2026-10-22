/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianChernoffTail
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianPositiveSignal

/-!
# The entire Gaussian localization tail at logarithmic variance

The optimized tilt is lambda=2/a, the variance is a^2*log(X),
and the tail begins at (a^2+2*a)*log(X). The physical factor 2*X
is included, leaving exponent -1+a^2/2 and one logarithm.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Filter

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def gaussianLocalizationTail (X a : Real) : Real :=
  2 * X * integral volume
    ((Set.Ioi ((a ^ 2 + 2 * a) * Real.log X)).indicator (fun u : Real =>
      Real.exp u * (Real.log X + abs u) * logGaussianDensity (a ^ 2 * Real.log X) u))

theorem gaussianLocalizationTail_log_scale_bound
    (X a : Real) (ha : 0 < a) (hX : Real.exp 1 <= X) :
    gaussianLocalizationTail X a <=
      (2 * (2 + a ^ 2 + 2 * a + 2 * a ^ 2 / Real.pi)) *
        X ^ (-1 + a ^ 2 / 2) * Real.log X := by
  have hXPos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hLog : 1 <= Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using h
  have hLogPos : 0 < Real.log X := by linarith only [hLog]
  let V : Real := a ^ 2 * Real.log X
  let h : Real := (a ^ 2 + 2 * a) * Real.log X
  let lambda : Real := 2 / a
  have hV : 0 < V := mul_pos (sq_pos_of_pos ha) hLogPos
  have hLambda : 0 <= lambda := by dsimp only [lambda]; positivity
  have hTail := logGaussianDensity_chernoff_tail_bound V (Real.log X) h lambda
    hV hLogPos.le hLambda
  have hExponent :
      -lambda * h + V * (1 + lambda) ^ 2 / 2 =
        (-2 + a ^ 2 / 2) * Real.log X := by
    dsimp only [lambda, h, V]
    field_simp [ha.ne']
    <;> ring
  have hShift : V * (1 + lambda) = (a ^ 2 + 2 * a) * Real.log X := by
    dsimp only [V, lambda]
    field_simp [ha.ne']
    <;> ring
  have hShiftNonneg : 0 <= V * (1 + lambda) := by
    rw [hShift]
    positivity
  let r : Real := Real.sqrt (2 * V / Real.pi)
  have hrSq : r ^ (2 : Nat) = 2 * V / Real.pi :=
    Real.sq_sqrt (by positivity)
  have hrBound : r <= 1 + 2 * V / Real.pi := by
    nlinarith only [sq_nonneg (r - 1 / 2), hrSq]
  have hMoment : Real.log X + abs (V * (1 + lambda)) + r <=
      (2 + a ^ 2 + 2 * a + 2 * a ^ 2 / Real.pi) * Real.log X := by
    rw [abs_of_nonneg hShiftNonneg, hShift]
    dsimp only [V] at hrBound
    calc
      _ <= Real.log X + (a ^ 2 + 2 * a) * Real.log X +
          (1 + 2 * (a ^ 2 * Real.log X) / Real.pi) :=
        add_le_add (le_refl _) hrBound
      _ <= Real.log X + (a ^ 2 + 2 * a) * Real.log X +
          (Real.log X + 2 * (a ^ 2 * Real.log X) / Real.pi) :=
        add_le_add (le_refl _) (add_le_add hLog (le_refl _))
      _ = _ := by ring
  have hExponential :
      Real.exp (-lambda * h + V * (1 + lambda) ^ 2 / 2) = X ^ (-2 + a ^ 2 / 2) := by
    rw [hExponent, Real.rpow_def_of_pos hXPos]
    congr 1
    ring
  have hPower : X * X ^ (-2 + a ^ 2 / 2) = X ^ (-1 + a ^ 2 / 2) := by
    calc
      _ = X ^ (1 : Real) * X ^ (-2 + a ^ 2 / 2) := by rw [Real.rpow_one]
      _ = X ^ (1 + (-2 + a ^ 2 / 2)) := (Real.rpow_add hXPos _ _).symm
      _ = _ := by congr 1; ring
  rw [hExponential] at hTail
  have hWeight := mul_le_mul_of_nonneg_left hMoment
    (Real.rpow_pos_of_pos hXPos (-2 + a ^ 2 / 2)).le
  have hFinal := mul_le_mul_of_nonneg_left (hTail.trans hWeight)
    (by positivity : 0 <= 2 * X)
  change gaussianLocalizationTail X a <= _ at hFinal
  calc
    _ <= 2 * X * (X ^ (-2 + a ^ 2 / 2) *
        ((2 + a ^ 2 + 2 * a + 2 * a ^ 2 / Real.pi) * Real.log X)) := hFinal
    _ = (2 * (2 + a ^ 2 + 2 * a + 2 * a ^ 2 / Real.pi)) *
        (X * X ^ (-2 + a ^ 2 / 2)) * Real.log X := by ring
    _ = _ := by rw [hPower]

theorem gaussianLocalizationTail_eventually_nonneg (a : Real) (ha : 0 < a) :
    Filter.Eventually (fun X : Real => 0 <= gaussianLocalizationTail X a) atTop := by
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
  have hXPos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hLog : 0 < Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at h
    linarith only [h]
  have hV : 0 < a ^ 2 * Real.log X := mul_pos (sq_pos_of_pos ha) hLog
  apply mul_nonneg (by positivity : 0 <= 2 * X)
  apply integral_nonneg
  intro u
  apply Set.indicator_nonneg
  intro u hu
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (add_nonneg hLog.le (abs_nonneg _)))
    (logGaussianDensity_pos _ _ hV).le

theorem gaussianLocalizationTail_div_power_tendsto
    (a B : Real) (ha : 0 < a) (haSmall : a < 1 / 4) (hB : 0 < B) :
    Tendsto (fun X : Real => gaussianLocalizationTail X a / X ^ B) atTop (nhds 0) := by
  have hGap : -1 + a ^ 2 / 2 < B := by nlinarith
  let C : Real := 2 * (2 + a ^ 2 + 2 * a + 2 * a ^ 2 / Real.pi)
  have hUpper : Tendsto
      (fun X : Real => C * (X ^ (-1 + a ^ 2 / 2) * Real.log X / X ^ B))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (gaussian_power_log_ratio_tendsto (-1 + a ^ 2 / 2) B hGap).const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
  . filter_upwards [gaussianLocalizationTail_eventually_nonneg a ha,
      eventually_ge_atTop (Real.exp 1)] with X hTail hX
    exact div_nonneg hTail
      (Real.rpow_nonneg ((Real.exp_pos 1).trans_le hX).le B)
  . filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
    have hBound := div_le_div_of_nonneg_right
      (gaussianLocalizationTail_log_scale_bound X a ha hX)
      (Real.rpow_nonneg ((Real.exp_pos 1).trans_le hX).le B)
    calc
      _ <= _ := hBound
      _ = C * (X ^ (-1 + a ^ 2 / 2) * Real.log X / X ^ B) := by
        dsimp only [C]
        ring

end PrimeFactorOscillations.PrimeClassDeletion
