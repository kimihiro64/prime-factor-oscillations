/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ModifiedLcmRemainder

/-!
# Negligible defect below the upper reciprocal-square band

Choose J=ceil(N^(1/3)) in the exact free-cutoff bound. The full lower-band
defect is at most 3*N^(-2/3)+1/N and vanishes on the critical scale.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Asymptotics

theorem modifiedLcmSmallDefect_bound_rpow (N : Nat) (hN : 0 < N) :
    modifiedLcmSmallDefect N <= 3 * (N : Real) ^ (-2 / 3 : Real) + 1 / (N : Real) := by
  have hNPos : (0 : Real) < N := by exact_mod_cast hN
  let y : Real := (N : Real) ^ (1 / 3 : Real)
  let J : Nat := Nat.ceil y
  have hy : 0 < y := Real.rpow_pos_of_pos hNPos _
  have hLow : y <= (J : Real) := Nat.le_ceil y
  have hUp : (J : Real) <= y + 1 := (Nat.ceil_lt_add_one hy.le).le
  have hJPos : (0 : Real) < J := hy.trans_le hLow
  have hJ : 1 <= J := by
    have hNat : 0 < J := by exact_mod_cast hJPos
    omega
  have hBound := (modifiedLcm_defect_error_bound N J hN hJ).2
  rw [modifiedLcm_defect_exact_split, add_sub_cancel_right] at hBound
  have hSquare : y ^ 2 <= (J : Real) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hLow)
      (add_nonneg (hy.le.trans hLow) hy.le)]
  have hInv := one_div_le_one_div_of_le (sq_pos_of_pos hy) hSquare
  have hRpow : y ^ 2 = (N : Real) ^ (2 / 3 : Real) := by
    dsimp [y]
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hNPos.le]
    norm_num
  have hInvEq : 1 / y ^ 2 = (N : Real) ^ (-2 / 3 : Real) := by
    rw [hRpow, show (-2 / 3 : Real) = -(2 / 3 : Real) by ring,
      Real.rpow_neg hNPos.le, one_div]
  have hDivEq : y / (N : Real) = (N : Real) ^ (-2 / 3 : Real) := by
    dsimp [y]
    rw [show (-2 / 3 : Real) = 1 / 3 - 1 by norm_num,
      Real.rpow_sub hNPos, Real.rpow_one]
  calc
    _ <= (J : Real) / (N : Real) + 2 / (J : Real) ^ (2 : Nat) := hBound
    _ <= (y + 1) / (N : Real) + 2 / y ^ 2 := by
      apply add_le_add (div_le_div_of_nonneg_right hUp hNPos.le)
      have h := mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : Real) <= 2)
      simpa only [mul_one_div] using h
    _ = y / (N : Real) + 1 / (N : Real) + 2 * (1 / y ^ 2) := by ring
    _ = _ := by rw [hInvEq, hDivEq]; ring

theorem tendsto_modifiedLcmSmallDefect_scaled :
    Tendsto (fun N : Nat => modifiedLcmSmallDefect N *
      Real.sqrt (N : Real) * Real.log (N : Real)) atTop (nhds (0 : Real)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hOne : Tendsto (fun N : Nat => Real.log (N : Real) / (N : Real) ^ (1 / 6 : Real))
      atTop (nhds (0 : Real)) := by
    exact (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 6)).tendsto_div_nhds_zero.comp hn
  have hTwo : Tendsto (fun N : Nat => Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real))
      atTop (nhds (0 : Real)) := by
    exact (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero.comp hn
  have hUpper := (hOne.const_mul 3).add hTwo
  simp only [mul_zero, zero_add] at hUpper
  apply squeeze_zero'
    (by
      filter_upwards [eventually_ge_atTop (1 : Nat)] with N hN
      have hE : 0 <= modifiedLcmSmallDefect N :=
        Finset.sum_nonneg (fun p _ => modifiedLcm_defect_nonneg N p)
      exact mul_nonneg (mul_nonneg hE (Real.sqrt_nonneg _))
        (Real.log_nonneg (by exact_mod_cast hN))) ?_ hUpper
  filter_upwards [eventually_ge_atTop (1 : Nat)] with N hN
  have hx : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hLog : 0 <= Real.log (N : Real) := Real.log_nonneg (by exact_mod_cast hN)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (modifiedLcmSmallDefect_bound_rpow N (by omega))
      (Real.sqrt_nonneg (N : Real))) hLog
  have hPowOne :
      (N : Real) ^ (-2 / 3 : Real) * (N : Real) ^ (1 / 2 : Real) =
        (N : Real) ^ (-1 / 6 : Real) := by
    rw [<- Real.rpow_add hx]
    norm_num
  have hPowTwo :
      (1 / (N : Real)) * (N : Real) ^ (1 / 2 : Real) =
        (N : Real) ^ (-1 / 2 : Real) := by
    rw [one_div, <- Real.rpow_neg_one, <- Real.rpow_add hx]
    norm_num
  apply h.trans_eq
  calc
    _ = 3 * ((N : Real) ^ (-2 / 3 : Real) * (N : Real) ^ (1 / 2 : Real)) *
        Real.log (N : Real) +
      ((1 / (N : Real)) * (N : Real) ^ (1 / 2 : Real)) * Real.log (N : Real) := by
      rw [Real.sqrt_eq_rpow]
      ring
    _ = 3 * (N : Real) ^ (-1 / 6 : Real) * Real.log (N : Real) +
        (N : Real) ^ (-1 / 2 : Real) * Real.log (N : Real) := by rw [hPowOne, hPowTwo]
    _ = _ := by
      rw [show (-1 / 6 : Real) = -(1 / 6 : Real) by ring,
        show (-1 / 2 : Real) = -(1 / 2 : Real) by ring,
        Real.rpow_neg hx.le, Real.rpow_neg hx.le]
      ring

end PrimeFactorOscillations
