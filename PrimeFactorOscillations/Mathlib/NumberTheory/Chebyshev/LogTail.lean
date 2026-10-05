/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Ring

/-!
# Logarithmic prime-power tails

The difference between the Chebyshev psi and theta functions contributes a
nonnegative, absolutely integrable tail bounded by 8 / sqrt x for x >= 3.
This controls the error when transferring theta-tail and psi-tail oscillations.

The pointwise estimate adapts the Apache-2.0 Robin1984 source
`Robin1984/NicolasLandau/NicolasOscillation.lean` at commit
bfa72aec0c25c8ee29cefe4449d778ff30412bee. The statements here use only Mathlib
objects; no Nicolas or Robin declaration is imported or assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Chebyshev

open Filter MeasureTheory Set

/-- The explicit prime-power error in the logarithmic theta/psi tail kernel. -/
theorem primePowerLogKernel_norm_le {t : Real} (ht : 3 < t) :
    norm ((Chebyshev.psi t - Chebyshev.theta t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) <=
      4 * t ^ (-(3 / 2 : Real)) := by
  have htPos : 0 < t := lt_trans (by norm_num) ht
  have htOne : 1 < t := lt_trans (by norm_num) ht
  have hLog : 0 < Real.log t := Real.log_pos htOne
  have hLogOne : 1 < Real.log t := by
    rw [Real.lt_log_iff_exp_lt htPos]
    exact lt_trans Real.exp_one_lt_three ht
  have hGapNonneg : 0 <= Chebyshev.psi t - Chebyshev.theta t :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi t)
  have hKernelNonneg : 0 <=
      (1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2 := by positivity
  have hGap := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log
    (le_trans (by norm_num) ht.le)
  rw [abs_of_nonneg hGapNonneg] at hGap
  have hInvLog : 1 / Real.log t <= 1 :=
    (div_le_one hLog).mpr hLogOne.le
  have hPower : Real.sqrt t / t ^ 2 = t ^ (-(3 / 2 : Real)) := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_natCast t 2, div_eq_mul_inv,
      <- Real.rpow_neg htPos.le, <- Real.rpow_add htPos]
    norm_num
  calc
    norm ((Chebyshev.psi t - Chebyshev.theta t) *
        ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) =
        (Chebyshev.psi t - Chebyshev.theta t) *
          ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hGapNonneg hKernelNonneg)]
    _ <= (2 * Real.sqrt t * Real.log t) *
        ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2) :=
      mul_le_mul_of_nonneg_right hGap hKernelNonneg
    _ = (2 * Real.sqrt t / t ^ 2) * (1 + 1 / Real.log t) := by
      field_simp [htPos.ne', hLog.ne']
    _ <= (2 * Real.sqrt t / t ^ 2) * 2 := by
      apply mul_le_mul_of_nonneg_left
      . linarith
      . positivity
    _ = 4 * t ^ (-(3 / 2 : Real)) := by
      rw [show 2 * Real.sqrt t / t ^ 2 =
        2 * (Real.sqrt t / t ^ 2) by ring, hPower]
      ring

theorem primePowerLogKernel_integrableOn {x : Real} (hx : 3 <= x) :
    IntegrableOn (fun t : Real => (Chebyshev.psi t - Chebyshev.theta t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) (Ioi x) := by
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  apply Integrable.mono' (g := fun t : Real => 4 * t ^ (-(3 / 2 : Real)))
  . exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hxPos).const_mul 4
  . have hKernelMeas : Measurable (fun t : Real =>
        (1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2) := by
      measurability
    exact ((Chebyshev.psi_mono.measurable.sub
      Chebyshev.theta_mono.measurable).mul hKernelMeas).aestronglyMeasurable
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact primePowerLogKernel_norm_le (hx.trans_lt ht)

theorem primePowerLogTail_bounds {x : Real} (hx : 3 <= x) :
    0 <= integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Chebyshev.psi t - Chebyshev.theta t) *
          ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) /\
    integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Chebyshev.psi t - Chebyshev.theta t) *
          ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) <=
      8 * x ^ (-(1 / 2 : Real)) := by
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hF := primePowerLogKernel_integrableOn hx
  have hG : IntegrableOn (fun t : Real => 4 * t ^ (-(3 / 2 : Real))) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hxPos).const_mul 4
  constructor
  . apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hLog : 0 < Real.log t := Real.log_pos
      (lt_of_lt_of_le (by norm_num : (1 : Real) < 3) (hx.trans ht.le))
    apply mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t))
    positivity
  . calc
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Chebyshev.psi t - Chebyshev.theta t) *
            ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) <=
          integral (volume.restrict (Ioi x))
            (fun t : Real => 4 * t ^ (-(3 / 2 : Real))) := by
        apply integral_mono_ae hF hG
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        apply (le_abs_self _).trans
        simpa only [Real.norm_eq_abs] using primePowerLogKernel_norm_le (hx.trans_lt ht)
      _ = 8 * x ^ (-(1 / 2 : Real)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hxPos]
        norm_num
        ring

end Chebyshev
