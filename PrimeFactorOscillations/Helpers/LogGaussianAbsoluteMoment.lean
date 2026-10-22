/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianDensityCalculus

/-!
# The exact absolute first moment of the normalized Gaussian

Both half-lines are integrated from the proved density derivative and
endpoint limits. The final constant is sqrt(2*V/pi), as stated in the paper.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set Filter

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianDensity_first_moment_Ioi
    (V : Real) (hV : 0 < V) :
    integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
      u * logGaussianDensity V u) = V * logGaussianDensity V 0 := by
  have hDeriv (u : Real) :
      HasDerivAt (fun v : Real => -V * logGaussianDensity V v)
        (u * logGaussianDensity V u) u := by
    have h := (logGaussianDensity_hasDerivAt V u).const_mul (-V)
    have he : -V * ((-u / V) * logGaussianDensity V u) =
        u * logGaussianDensity V u := by field_simp [hV.ne']
    simpa only [he] using! h
  have hInt := (logGaussianDensity_first_moment_integrable V hV).integrableOn
    (s := Ioi (0 : Real))
  have hLim : Tendsto (fun u : Real => -V * logGaussianDensity V u) atTop (nhds 0) := by
    simpa only [mul_zero] using (logGaussianDensity_tendsto_atTop V hV).const_mul (-V)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u _ => hDeriv u) hInt hLim
  simpa only [zero_sub, neg_mul, neg_neg] using h

theorem logGaussianDensity_first_moment_Iic
    (V : Real) (hV : 0 < V) :
    integral (volume.restrict (Iic (0 : Real))) (fun u : Real =>
      -u * logGaussianDensity V u) = V * logGaussianDensity V 0 := by
  have hDeriv (u : Real) :
      HasDerivAt (fun v : Real => V * logGaussianDensity V v)
        (-u * logGaussianDensity V u) u := by
    have h := (logGaussianDensity_hasDerivAt V u).const_mul V
    have he : V * ((-u / V) * logGaussianDensity V u) =
        -u * logGaussianDensity V u := by field_simp [hV.ne']
    simpa only [he] using! h
  have hIntFull : Integrable (fun u : Real => -u * logGaussianDensity V u) := by
    simpa only [Pi.neg_apply, neg_mul] using!
      (logGaussianDensity_first_moment_integrable V hV).neg
  have hInt := hIntFull.integrableOn (s := Iic (0 : Real))
  have hLim : Tendsto (fun u : Real => V * logGaussianDensity V u) atBot (nhds 0) := by
    simpa only [mul_zero] using (logGaussianDensity_tendsto_atBot V hV).const_mul V
  have h := integral_Iic_of_hasDerivAt_of_tendsto'
    (fun u _ => hDeriv u) hInt hLim
  simpa only [sub_zero] using h

theorem logGaussianDensity_abs_moment_integrable
    (V : Real) (hV : 0 < V) :
    Integrable (fun u : Real => abs u * logGaussianDensity V u) := by
  apply (logGaussianDensity_first_moment_integrable V hV).norm.congr
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (logGaussianDensity_pos V u hV)]

theorem logGaussianDensity_abs_moment
    (V : Real) (hV : 0 < V) :
    integral volume (fun u : Real => abs u * logGaussianDensity V u) =
      Real.sqrt (2 * V / Real.pi) := by
  have hSplit := integral_add_compl (s := Iic (0 : Real)) measurableSet_Iic
    (logGaussianDensity_abs_moment_integrable V hV)
  simp only [compl_Iic] at hSplit
  have hLeft : integral (volume.restrict (Iic (0 : Real)))
      (fun u : Real => abs u * logGaussianDensity V u) = V * logGaussianDensity V 0 := by
    calc
      _ = integral (volume.restrict (Iic (0 : Real)))
          (fun u : Real => -u * logGaussianDensity V u) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro u hu
        dsimp only
        rw [abs_of_nonpos hu]
      _ = _ := logGaussianDensity_first_moment_Iic V hV
  have hRight : integral (volume.restrict (Ioi (0 : Real)))
      (fun u : Real => abs u * logGaussianDensity V u) = V * logGaussianDensity V 0 := by
    calc
      _ = integral (volume.restrict (Ioi (0 : Real)))
          (fun u : Real => u * logGaussianDensity V u) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        dsimp only
        rw [abs_of_pos hu]
      _ = _ := logGaussianDensity_first_moment_Ioi V hV
  rw [hLeft, hRight] at hSplit
  have hFull : integral volume (fun u : Real => abs u * logGaussianDensity V u) =
      2 * V * logGaussianDensity V 0 := by
    linear_combination -hSplit
  rw [hFull, logGaussianDensity]
  simp only [zero_pow (by decide : Not (2 = 0)), neg_zero, zero_div, Real.exp_zero]
  let d : Real := Real.sqrt (2 * Real.pi * V)
  let r : Real := Real.sqrt (2 * V / Real.pi)
  have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hr : 0 <= r := Real.sqrt_nonneg _
  have hdSq : d ^ (2 : Nat) = 2 * Real.pi * V := Real.sq_sqrt (by positivity)
  have hrSq : r ^ (2 : Nat) = 2 * V / Real.pi := Real.sq_sqrt (by positivity)
  have hSquare : (d * r) ^ (2 : Nat) = (2 * V) ^ (2 : Nat) := by
    rw [mul_pow, hdSq, hrSq]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hProduct : d * r = 2 * V := by
    nlinarith only [hSquare, mul_nonneg hd.le hr, hV]
  change 2 * V * (1 / d) = r
  have hResult : (2 * V) / d = r := by
    apply (div_eq_iff hd.ne').mpr
    simpa only [mul_comm] using hProduct.symm
  simpa only [mul_one_div] using hResult

end PrimeFactorOscillations.PrimeClassDeletion
