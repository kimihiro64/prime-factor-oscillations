/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LcmStripFiniteTail
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.ZeroConstantBound

/-!
# Explicit positive margin at the seven-eighths strip

Exact estimates for a fixed twenty-four-block prime tail. These bounds
provide a positive margin after the complete seven-eighths spectral loss.
They do not assert the zero-free strip used by the eventual application.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

theorem lcmStrip_eighth_power (s : Real) (hs : 0 < s) (j : Nat) :
    ((s ^ 8) ^ j) ^ (7 / 8 : Real) = (s ^ 7) ^ j := by
  calc
    _ = (s ^ ((8 * j : Nat) : Real)) ^ (7 / 8 : Real) := by
      rw [Real.rpow_natCast, pow_mul]
    _ = s ^ (((8 * j : Nat) : Real) * (7 / 8 : Real)) :=
      (Real.rpow_mul hs.le _ _).symm
    _ = s ^ ((7 * j : Nat) : Real) := by
      congr 1
      push_cast
      ring
    _ = _ := by rw [Real.rpow_natCast, pow_mul]

theorem lcmStrip_eighth_term (s : Real) (hs : 0 < s) (j : Nat) :
    (((s ^ 8) ^ (j + 1)) ^ (7 / 8 : Real) - ((s ^ 8) ^ j) ^ (7 / 8 : Real)) /
        (s ^ 8) ^ (j + 1) =
      ((1 / s) - (1 / s) ^ 8) * (1 / s) ^ j := by
  rw [lcmStrip_eighth_power s hs (j + 1), lcmStrip_eighth_power s hs j]
  have h7 : (s ^ 7) ^ j = (s ^ j) ^ 7 := by
    rw [<- pow_mul, Nat.mul_comm 7 j, pow_mul]
  have h8 : (s ^ 8) ^ j = (s ^ j) ^ 8 := by
    rw [<- pow_mul, Nat.mul_comm 8 j, pow_mul]
  rw [pow_succ (s ^ 7) j, pow_succ (s ^ 8) j, h7, h8]
  simp only [div_pow, one_pow]
  field_simp [hs.ne', pow_ne_zero _ hs.ne']

theorem lcmStripFiniteTailCoefficient_seven_eighths (m : Nat) :
    lcmStripFiniteTailCoefficient (7 / 8) ((12 / 11 : Real) ^ 8) m =
      12 * (1 - (11 / 12 : Real) ^ 8) -
        (12 * (1 - (11 / 12 : Real) ^ 8) - 1) * (11 / 12 : Real) ^ m := by
  induction m with
  | zero =>
      simp only [lcmStripFiniteTailCoefficient, Finset.sum_range_zero, add_zero, pow_zero]
      ring
  | succ m ih =>
      have hStep : lcmStripFiniteTailCoefficient (7 / 8) ((12 / 11 : Real) ^ 8) (m + 1) =
          lcmStripFiniteTailCoefficient (7 / 8) ((12 / 11 : Real) ^ 8) m +
            (((((12 / 11 : Real) ^ 8) ^ (m + 1)) ^ (7 / 8 : Real) -
              (((12 / 11 : Real) ^ 8) ^ m) ^ (7 / 8 : Real)) /
                ((12 / 11 : Real) ^ 8) ^ (m + 1)) := by
        simp only [lcmStripFiniteTailCoefficient, Finset.sum_range_succ]
        ring
      rw [hStep, lcmStrip_eighth_term (12 / 11) (by norm_num) m, ih]
      rw [show (1 / (12 / 11) : Real) = 11 / 12 by norm_num, pow_succ]
      ring

theorem lcmStripFiniteTailCoefficient_twenty_four :
    (43 / 8 : Real) < lcmStripFiniteTailCoefficient (7 / 8) ((12 / 11 : Real) ^ 8) 24 := by
  rw [lcmStripFiniteTailCoefficient_seven_eighths]
  norm_num

theorem lcm_exp_neg_four_lower :
    (4 / 11 : Real) ^ 4 < Real.exp (-4) := by
  have hSeries := Real.sum_range_le_log_div (x := (7 / 15 : Real))
    (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hSeries
  have hLog : (1 : Real) < Real.log (11 / 4 : Real) := by linarith
  have hLog4 : (4 : Real) < Real.log ((11 / 4 : Real) ^ 4) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hLog]
  have hExp := Real.exp_lt_exp.mpr hLog4
  rw [Real.exp_log (by norm_num : (0 : Real) < (11 / 4 : Real) ^ 4)] at hExp
  have hCancel : Real.exp 4 * Real.exp (-4) = 1 := by
    rw [<- Real.exp_add]
    norm_num
  have h := mul_lt_mul_of_pos_right hExp
    (show 0 < (4 / 11 : Real) ^ 4 * Real.exp (-4) by positivity)
  nlinarith only [h, hCancel]

theorem lcmStrip_seven_eighths_loss_lt (beta : Real) (hBeta : beta <= 1 / 20) :
    9 * beta / (2 * Real.sqrt 7) < (3 / 35 : Real) := by
  have hSq : (Real.sqrt 7) ^ 2 = (7 : Real) := Real.sq_sqrt (by norm_num)
  have hRoot : (21 / 8 : Real) < Real.sqrt 7 := by
    nlinarith [Real.sqrt_nonneg 7]
  have hInv := one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 21 / 8) hRoot
  have hCap := mul_lt_mul_of_pos_left hInv (by norm_num : (0 : Real) < 9 / 40)
  rw [show (9 / 40 : Real) * (1 / (21 / 8)) = 3 / 35 by norm_num] at hCap
  have hBetaScaled := mul_le_mul_of_nonneg_right hBeta
    (show 0 <= 9 / (2 * Real.sqrt 7) by positivity)
  have hLe : 9 * beta / (2 * Real.sqrt 7) <= (9 / 40) * (1 / Real.sqrt 7) := by
    convert hBetaScaled using 1 <;> ring
  exact hLe.trans_lt hCap

theorem lcmStrip_seven_eighths_supply_gt :
    (1376 / 14641 : Real) <
      lcmStripFiniteTailCoefficient (7 / 8) ((12 / 11 : Real) ^ 8) 24 * Real.exp (-4) := by
  have hC := lcmStripFiniteTailCoefficient_twenty_four
  have hE := lcm_exp_neg_four_lower
  have h1 := mul_lt_mul_of_pos_left hE (by norm_num : (0 : Real) < 43 / 8)
  rw [show (43 / 8 : Real) * (4 / 11) ^ 4 = 1376 / 14641 by norm_num] at h1
  have h2 := mul_lt_mul_of_pos_right hC (Real.exp_pos (-4))
  exact h1.trans h2

theorem lcmStrip_seven_eighths_explicit_margin :
    (1 / 200 : Real) <
      lcmStripFiniteTailCoefficient (7 / 8) ((12 / 11 : Real) ^ 8) 24 * Real.exp (-4) -
        3 / 35 := by
  linarith only [lcmStrip_seven_eighths_supply_gt]

end PrimeFactorOscillations
