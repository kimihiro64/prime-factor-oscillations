/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPrimeSquareBias
import PrimeFactorOscillations.Helpers.NicolasTiltedIntegral

/-!
# The full zero wave in the tilted theta integral

The unconditional integral error is carried through the exact RH scale.
Both the reciprocal-square-root error and logarithmic spectral remainder
remain visible, with explicit constants and all nonnegative tilts allowed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter Robin1984

def nicolasThetaWaveErrorConstant : Real :=
  10 + 45 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
    4 * Real.log (2 * Real.pi) + (Real.log 4 + 4) * (79 / 3 : Real)

theorem nicolasTiltedIntegral_wave_normalized_error
    (hRH : RiemannHypothesis) {z x : Real} (hz : 0 <= z)
    (hx : 4 <= x) (hlog : 1 <= Real.log x) :
    |nicolasTiltedIntegral z x * (x ^ (1 / 2 : Real) * Real.log x) +
      z * (2 + nicolasZeroWave x)| <=
        nicolasTiltedIntegralErrorConstant z * x ^ (-(1 / 2 : Real)) +
          z * nicolasThetaWaveErrorConstant / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := by linarith
  let s : Real := x ^ (1 / 2 : Real) * Real.log x
  have hs : 0 < s := mul_pos (Real.rpow_pos_of_pos hx0 _) hl
  have hPower : x ^ (1 / 2 : Real) / x = x ^ (-(1 / 2 : Real)) := by
    rw [div_eq_mul_inv, <- Real.rpow_neg_one, <- Real.rpow_add hx0]
    norm_num
  have hRecip : x ^ (-(1 / 2 : Real)) * x ^ (1 / 2 : Real) = 1 := by
    rw [<- Real.rpow_add hx0]
    norm_num
  have hTail := mul_le_mul_of_nonneg_right
    (nicolasTiltedIntegral_error hz (by linarith : 3 <= x)) hs.le
  have hTailEq :
      (nicolasTiltedIntegralErrorConstant z / (x * Real.log x)) * s =
        nicolasTiltedIntegralErrorConstant z * x ^ (-(1 / 2 : Real)) := by
    calc
      _ = nicolasTiltedIntegralErrorConstant z * (x ^ (1 / 2 : Real) / x) := by
        dsimp [s]
        field_simp
      _ = _ := by rw [hPower]
  rw [hTailEq, <- abs_of_pos hs, <- abs_mul] at hTail
  have hK := mul_le_mul_of_nonneg_right (nicolasK_wave_uniform_error hRH hx hlog) hs.le
  change |nicolasK x + (2 + nicolasZeroWave x) / s| * s <=
    (nicolasThetaWaveErrorConstant * x ^ (-(1 / 2 : Real)) *
      Inv.inv ((Real.log x) ^ 2)) * s at hK
  have hKEq :
      (nicolasThetaWaveErrorConstant * x ^ (-(1 / 2 : Real)) *
        Inv.inv ((Real.log x) ^ 2)) * s =
        nicolasThetaWaveErrorConstant / Real.log x := by
    calc
      _ = nicolasThetaWaveErrorConstant *
          (x ^ (-(1 / 2 : Real)) * x ^ (1 / 2 : Real)) / Real.log x := by
        dsimp [s]
        field_simp
      _ = _ := by rw [hRecip]; ring
  rw [hKEq] at hK
  have hKAbs : |(nicolasK x + (2 + nicolasZeroWave x) / s) * s| <=
      nicolasThetaWaveErrorConstant / Real.log x := by
    simpa only [abs_mul, abs_of_pos hs] using hK
  have hArg : (nicolasK x + (2 + nicolasZeroWave x) / s) * s =
      nicolasK x * s + (2 + nicolasZeroWave x) := by field_simp
  rw [hArg] at hKAbs
  have hExact : nicolasTiltedIntegral z x * s + z * (2 + nicolasZeroWave x) =
      (nicolasTiltedIntegral z x - z * nicolasK x) * s +
        z * (nicolasK x * s + (2 + nicolasZeroWave x)) := by ring
  change |nicolasTiltedIntegral z x * s + z * (2 + nicolasZeroWave x)| <= _
  rw [hExact]
  calc
    _ <= |(nicolasTiltedIntegral z x - z * nicolasK x) * s| +
        |z * (nicolasK x * s + (2 + nicolasZeroWave x))| := abs_add_le _ _
    _ = |(nicolasTiltedIntegral z x - z * nicolasK x) * s| +
        z * |nicolasK x * s + (2 + nicolasZeroWave x)| := by
      simp only [abs_mul, abs_of_nonneg hz]
    _ <= nicolasTiltedIntegralErrorConstant z * x ^ (-(1 / 2 : Real)) +
        z * (nicolasThetaWaveErrorConstant / Real.log x) :=
      add_le_add hTail (mul_le_mul_of_nonneg_left hKAbs hz)
    _ = _ := by ring

theorem tendsto_nicolasTiltedIntegral_wave_error
    (hRH : RiemannHypothesis) (z : Real) (hz : 0 <= z) :
    Tendsto (fun x : Real =>
      nicolasTiltedIntegral z x * (x ^ (1 / 2 : Real) * Real.log x) +
        z * (2 + nicolasZeroWave x)) atTop (nhds 0) := by
  have hRoot : Tendsto (fun x : Real => x ^ (-(1 / 2 : Real))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : Real) < 1 / 2)
  have hLog : Tendsto (fun x : Real => Inv.inv (Real.log x)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have h1 : Tendsto (fun x : Real =>
      nicolasTiltedIntegralErrorConstant z * x ^ (-(1 / 2 : Real))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hRoot
  have h2 : Tendsto (fun x : Real =>
      (z * nicolasThetaWaveErrorConstant) * Inv.inv (Real.log x)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hLog
  have hSum : Tendsto (fun x : Real =>
      nicolasTiltedIntegralErrorConstant z * x ^ (-(1 / 2 : Real)) +
        z * nicolasThetaWaveErrorConstant / Real.log x) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, add_zero] using h1.add h2
  apply Metric.tendsto_atTop.mpr
  intro epsilon hEpsilon
  apply eventually_atTop.mp
  filter_upwards [hSum.eventually_lt_const hEpsilon, eventually_ge_atTop (4 : Real),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x he hx hlog
  rw [Real.dist_eq, sub_zero]
  exact (nicolasTiltedIntegral_wave_normalized_error hRH hz hx hlog).trans_lt he

end PrimeFactorOscillations
