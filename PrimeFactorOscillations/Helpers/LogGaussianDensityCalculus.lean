/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Helpers.LogGaussianMoment

/-!
# Real Gaussian calculus for the full prime-power correction

The exact derivative, first-moment integrability and both endpoint limits
are proved for the paper's normalized density. No moment constant is relaxed.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Filter

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianDensity_pos (V u : Real) (hV : 0 < V) :
    0 < logGaussianDensity V u := by
  unfold logGaussianDensity
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (by positivity))

theorem logGaussianDensity_hasDerivAt (V u : Real) :
    HasDerivAt (logGaussianDensity V) ((-u / V) * logGaussianDensity V u) u := by
  have hInner : HasDerivAt (fun v : Real => -v ^ 2 / (2 * V)) (-u / V) u := by
    convert (((hasDerivAt_id u).pow 2).neg.div_const (2 * V)) using 1
    . funext v
      rfl
    . norm_num [id_eq]
      <;> ring
  have h := hInner.exp.div_const (Real.sqrt (2 * Real.pi * V))
  convert h using 1
  . funext v
    rfl
  . dsimp only [logGaussianDensity]
    ring

theorem logGaussianDensity_first_moment_integrable
    (V : Real) (hV : 0 < V) :
    Integrable (fun u : Real => u * logGaussianDensity V u) := by
  have hb : 0 < 1 / (2 * V) := by positivity
  have h := (integrable_mul_exp_neg_mul_sq hb).div_const (Real.sqrt (2 * Real.pi * V))
  apply h.congr
  filter_upwards with u
  have he : -(1 / (2 * V)) * u ^ 2 = -u ^ 2 / (2 * V) := by ring
  dsimp only [logGaussianDensity]
  rw [he]
  ring

theorem logGaussianDensity_tendsto_atTop (V : Real) (hV : 0 < V) :
    Tendsto (logGaussianDensity V) atTop (nhds 0) := by
  have hInner : Tendsto (fun u : Real => -u ^ 2 / (2 * V)) atTop atBot := by
    apply tendsto_atBot.2
    intro b
    filter_upwards [eventually_ge_atTop (max 1 (-b * (2 * V)))] with u hu
    have huOne : 1 <= u := (le_max_left _ _).trans hu
    have huB : -b * (2 * V) <= u := (le_max_right _ _).trans hu
    have hSq : u <= u ^ 2 := by nlinarith only [huOne]
    calc
      _ <= (b * (2 * V)) / (2 * V) :=
        div_le_div_of_nonneg_right (by linarith only [huB, hSq]) (by positivity)
      _ = b := by field_simp [hV.ne']
  have h := (Real.tendsto_exp_atBot.comp hInner).div_const
    (Real.sqrt (2 * Real.pi * V))
  simpa only [zero_div, logGaussianDensity, Function.comp_apply] using! h

theorem logGaussianDensity_tendsto_atBot (V : Real) (hV : 0 < V) :
    Tendsto (logGaussianDensity V) atBot (nhds 0) := by
  have hInner : Tendsto (fun u : Real => -u ^ 2 / (2 * V)) atBot atBot := by
    apply tendsto_atBot.2
    intro b
    filter_upwards [eventually_le_atBot (min (-1) (b * (2 * V)))] with u hu
    have huOne : u <= -1 := hu.trans (min_le_left _ _)
    have huB : u <= b * (2 * V) := hu.trans (min_le_right _ _)
    have hSq : -u <= u ^ 2 := by nlinarith only [huOne]
    calc
      _ <= (b * (2 * V)) / (2 * V) :=
        div_le_div_of_nonneg_right (by linarith only [huB, hSq]) (by positivity)
      _ = b := by field_simp [hV.ne']
  have h := (Real.tendsto_exp_atBot.comp hInner).div_const
    (Real.sqrt (2 * Real.pi * V))
  simpa only [zero_div, logGaussianDensity, Function.comp_apply] using! h

end PrimeFactorOscillations.PrimeClassDeletion
