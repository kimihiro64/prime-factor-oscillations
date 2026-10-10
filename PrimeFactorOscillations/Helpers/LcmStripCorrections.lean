/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeFactorOscillations.Helpers.LcmNormalizedComparison

/-!
# The complete modified-LCM corrections below the square-root scale

The height correction, prime-power defect and remainder vanish at the
N^(1-b) log N scale for every fixed b > 1/2. Each proof rescales the
existing unconditional square-root limit; no signed contribution is dropped.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Filter

theorem tendsto_lcm_strip_scale_of_sqrt_scale
    (f : Nat -> Real) (L b : Real) (hb : 1 / 2 < b)
    (h : Tendsto (fun N : Nat => f N * Real.sqrt (N : Real) * Real.log (N : Real))
      atTop (nhds L)) :
    Tendsto (fun N : Nat => f N * (N : Real) ^ (1 - b) * Real.log (N : Real))
      atTop (nhds 0) := by
  have hPow : Tendsto (fun N : Nat => (N : Real) ^ (-(b - 1 / 2)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hb)).comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun N : Nat => (N : Real)) atTop atTop)
  have hProduct := h.mul hPow
  rw [mul_zero] at hProduct
  apply hProduct.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with N hN
  have hx : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hP : Real.sqrt (N : Real) * (N : Real) ^ (-(b - 1 / 2)) =
      (N : Real) ^ (1 - b) := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_add hx]
    congr 1
    ring
  calc
    _ = f N * (Real.sqrt (N : Real) * (N : Real) ^ (-(b - 1 / 2))) *
        Real.log (N : Real) := by ring
    _ = _ := by rw [hP]

theorem tendsto_modifiedLcm_heightCorrection_strip_scaled
    (b : Real) (hb : 1 / 2 < b) :
    Tendsto (fun N : Nat => modifiedLcmHeightCorrection N *
      (N : Real) ^ (1 - b) * Real.log (N : Real)) atTop (nhds 0) :=
  tendsto_lcm_strip_scale_of_sqrt_scale _ _ b hb
    tendsto_modifiedLcm_heightCorrection_scaled

theorem tendsto_modifiedLcm_defect_strip_scaled
    (b : Real) (hb : 1 / 2 < b) :
    Tendsto (fun N : Nat => lcmDefectSum (modifiedLcm N) *
      (N : Real) ^ (1 - b) * Real.log (N : Real)) atTop (nhds 0) :=
  tendsto_lcm_strip_scale_of_sqrt_scale _ _ b hb
    tendsto_modifiedLcm_defect_scaled

theorem tendsto_modifiedLcm_remainder_strip_scaled
    (b : Real) (hb : 1 / 2 < b) :
    Tendsto (fun N : Nat => lcmDefectRemainder (modifiedLcm N) *
      (N : Real) ^ (1 - b) * Real.log (N : Real)) atTop (nhds 0) :=
  tendsto_lcm_strip_scale_of_sqrt_scale _ _ b hb
    tendsto_modifiedLcm_remainder_scaled

end PrimeFactorOscillations
