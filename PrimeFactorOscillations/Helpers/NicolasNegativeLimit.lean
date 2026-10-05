/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasNegativeEnvelope
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.ZeroConstantBound

/-!
# The eventual negative Nicolas margin under RH

The proved envelope, multiplied by x^(1/2)*log(x), tends to beta-2.
Since beta <= 1/20, it dominates every fixed reciprocal-cutoff margin.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

noncomputable section

def nicolasRHNormalizedEnvelope (x : Real) : Real :=
  let v := Inv.inv (Real.log x)
  let b := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  (b - 2) + (b + 2) * v + 4 * b * v ^ 2 +
    (b * x ^ (-(1 / 4 : Real))) * (2 + 2 * v + (16 / 3 : Real) * v ^ 2) +
    Real.log (2 * Real.pi) * x ^ (-(1 / 2 : Real)) +
    4 * (Real.log x / x ^ (1 / 2 : Real))

theorem nicolasRHUpperEnvelope_mul_scale {x : Real} (hx : 1 < x) :
    nicolasRHUpperEnvelope x * (x ^ (1 / 2 : Real) * Real.log x) =
      nicolasRHNormalizedEnvelope x := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLog : Not (Real.log x = 0) := (Real.log_pos hx).ne'
  have hHalf : x ^ (-(1 / 2 : Real)) * x ^ (1 / 2 : Real) = 1 := by
    rw [<- Real.rpow_add hxPos]
    norm_num
  have hQuarter :
      x ^ (-(3 / 4 : Real)) * x ^ (1 / 2 : Real) = x ^ (-(1 / 4 : Real)) := by
    rw [<- Real.rpow_add hxPos]
    norm_num
  have hInv : Inv.inv x = x ^ (-(1 : Real)) := by rw [Real.rpow_neg_one]
  have hRatio : x ^ (1 / 2 : Real) / x = x ^ (-(1 / 2 : Real)) := by
    rw [div_eq_mul_inv, hInv, <- Real.rpow_add hxPos]
    norm_num
  have hNeg : x ^ (-(1 / 2 : Real)) = Inv.inv (x ^ (1 / 2 : Real)) := by
    rw [Real.rpow_neg hxPos.le]
  let L : Real := Real.log x
  let b : Real := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  have hReduction :
      nicolasRHUpperEnvelope x * (x ^ (1 / 2 : Real) * Real.log x) =
      (x ^ (-(1 / 2 : Real)) * x ^ (1 / 2 : Real)) *
          ((b - 2) + (b + 2) * Inv.inv L + 4 * b * (Inv.inv L) ^ 2) +
        b * (x ^ (-(3 / 4 : Real)) * x ^ (1 / 2 : Real)) *
          (2 + 2 * Inv.inv L + (16 / 3 : Real) * (Inv.inv L) ^ 2) +
        Real.log (2 * Real.pi) * (x ^ (1 / 2 : Real) / x) +
        4 * L * (x ^ (1 / 2 : Real) / x) := by
    dsimp [nicolasRHUpperEnvelope, L, b]
    field_simp [hxPos.ne', hLog] <;> ring
  rw [hHalf, hQuarter, hRatio] at hReduction
  calc
    nicolasRHUpperEnvelope x * (x ^ (1 / 2 : Real) * Real.log x) = _ := hReduction
    _ = nicolasRHNormalizedEnvelope x := by
      dsimp [nicolasRHNormalizedEnvelope, L, b]
      simp only [div_eq_mul_inv, Real.rpow_neg hxPos.le]
      ring

theorem tendsto_nicolasRHNormalizedEnvelope :
    Tendsto nicolasRHNormalizedEnvelope atTop
      (nhds (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) - 2)) := by
  let b : Real := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  have hInv : Tendsto (fun x : Real => Inv.inv (Real.log x)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hQuarter : Tendsto (fun x : Real => x ^ (-(1 / 4 : Real))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : Real) < 1 / 4)
  have hHalf : Tendsto (fun x : Real => x ^ (-(1 / 2 : Real))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : Real) < 1 / 2)
  have hLogRatio : Tendsto (fun x : Real => Real.log x / x ^ (1 / 2 : Real))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero
  have hExpression : Tendsto (fun x : Real =>
      (b - 2) + (b + 2) * Inv.inv (Real.log x) +
        4 * b * (Inv.inv (Real.log x)) ^ 2 +
        (b * x ^ (-(1 / 4 : Real))) *
          (2 + 2 * Inv.inv (Real.log x) + (16 / 3 : Real) * (Inv.inv (Real.log x)) ^ 2) +
        Real.log (2 * Real.pi) * x ^ (-(1 / 2 : Real)) +
        4 * (Real.log x / x ^ (1 / 2 : Real))) atTop
      (nhds ((b - 2) + (b + 2) * 0 + 4 * b * 0 ^ 2 +
        (b * 0) * (2 + 2 * 0 + (16 / 3 : Real) * 0 ^ 2) +
        Real.log (2 * Real.pi) * 0 + 4 * 0)) :=
    (((((tendsto_const_nhds.add (tendsto_const_nhds.mul hInv)).add
      (tendsto_const_nhds.mul (hInv.pow 2))).add
      ((tendsto_const_nhds.mul hQuarter).mul
        ((tendsto_const_nhds.add (tendsto_const_nhds.mul hInv)).add
          (tendsto_const_nhds.mul (hInv.pow 2))))).add
      (tendsto_const_nhds.mul hHalf)).add
      (tendsto_const_nhds.mul hLogRatio))
  unfold nicolasRHNormalizedEnvelope
  dsimp only
  dsimp only [b] at hExpression
  simpa only [show (0 : Real) ^ 2 = 0 by norm_num,
    mul_zero, zero_mul, add_zero, zero_add] using hExpression

theorem tendsto_nicolasRHUpperEnvelope_scaled :
    Tendsto (fun x : Real =>
      nicolasRHUpperEnvelope x * (x ^ (1 / 2 : Real) * Real.log x)) atTop
      (nhds (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) - 2)) := by
  have hEq : Filter.EventuallyEq atTop
      (fun x : Real => nicolasRHUpperEnvelope x * (x ^ (1 / 2 : Real) * Real.log x))
      nicolasRHNormalizedEnvelope := by
    filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
    exact nicolasRHUpperEnvelope_mul_scale hx
  exact tendsto_nicolasRHNormalizedEnvelope.congr' hEq.symm

theorem eventually_nicolasLog_lt_neg_div_of_RH
    (hRH : RiemannHypothesis) (C : Real) :
    Filter.Eventually (fun x : Real =>
      nicolasLogMertensOscillation x < -C / x) atTop := by
  have hMain : Filter.Eventually (fun x : Real =>
      nicolasRHUpperEnvelope x * (x ^ (1 / 2 : Real) * Real.log x) < -1) atTop :=
    tendsto_nicolasRHUpperEnvelope_scaled.eventually_lt_const
      (by linarith [robin_zero_constant_le_one_twentieth])
  have hLogRatio : Tendsto (fun x : Real => Real.log x / x ^ (1 / 2 : Real))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero
  have hSmall : Tendsto (fun x : Real =>
      C * (Real.log x / x ^ (1 / 2 : Real))) atTop (nhds 0) := by
    have hMul : Tendsto (fun x : Real =>
        C * (Real.log x / x ^ (1 / 2 : Real))) atTop (nhds (C * 0)) :=
      tendsto_const_nhds.mul hLogRatio
    simpa using hMul
  have hSmallOne := hSmall.eventually_lt_const (by norm_num : (0 : Real) < 1)
  filter_upwards [hMain, hSmallOne, eventually_ge_atTop (4 : Real)] with x hMainX hSmallX hx
  have hxOne : 1 < x := by linarith
  have hxPos : 0 < x := by linarith
  have hPowerPos : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hxPos _
  have hScalePos : 0 < x ^ (1 / 2 : Real) * Real.log x :=
    mul_pos hPowerPos (Real.log_pos hxOne)
  have hUpper := mul_le_mul_of_nonneg_right
    (nicolasLog_le_RH_upper_envelope hRH hx) hScalePos.le
  have hSquare : (x ^ (1 / 2 : Real)) ^ (2 : Nat) = x := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hxPos.le]
    norm_num
  have hRatio : x ^ (1 / 2 : Real) / x = 1 / x ^ (1 / 2 : Real) := by
    calc
      x ^ (1 / 2 : Real) / x =
          x ^ (1 / 2 : Real) / ((x ^ (1 / 2 : Real)) ^ (2 : Nat)) :=
        congrArg (fun t : Real => x ^ (1 / 2 : Real) / t) hSquare.symm
      _ = 1 / x ^ (1 / 2 : Real) := by field_simp [hPowerPos.ne'] <;> ring
  have hTarget : (-C / x) * (x ^ (1 / 2 : Real) * Real.log x) =
      -C * (Real.log x / x ^ (1 / 2 : Real)) := by
    calc
      (-C / x) * (x ^ (1 / 2 : Real) * Real.log x) =
          -(C * Real.log x) * (x ^ (1 / 2 : Real) / x) := by ring
      _ = -(C * Real.log x) * (1 / x ^ (1 / 2 : Real)) := by rw [hRatio]
      _ = -C * (Real.log x / x ^ (1 / 2 : Real)) := by ring
  by_contra hNot
  have hOpposite := mul_le_mul_of_nonneg_right (le_of_not_gt hNot) hScalePos.le
  rw [hTarget] at hOpposite
  linarith

theorem eventually_nicolasLog_nat_lt_neg_div_of_RH
    (hRH : RiemannHypothesis) (C : Real) :
    Filter.Eventually (fun N : Nat =>
      nicolasLogMertensOscillation (N : Real) < -C / (N : Real)) atTop := by
  exact (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : Nat => (N : Real)) atTop atTop).eventually
      (eventually_nicolasLog_lt_neg_div_of_RH hRH C)

end

end PrimeFactorOscillations
