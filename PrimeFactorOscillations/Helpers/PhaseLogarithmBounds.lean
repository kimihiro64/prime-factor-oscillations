/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CompensatedXiConstants

/-! # Scalar and frequency enclosures for the signed height-sixty certificate -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem phase_log_seven_bounds :
    And ((1945910148 / 1000000000 : Real) <= Real.log 7)
      (Real.log 7 <= 1945910151 / 1000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := (1 / 8 : Real)) (by norm_num) 12
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : Real) = 2 ^ (3 : Nat) by norm_num, Real.log_pow]
    norm_num
  rw [show (1 - (1 / 8 : Real)) = 7 / 8 by norm_num,
    Real.log_div (by norm_num) (by norm_num), h8] at h
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  exact And.intro (by linarith only [hl, hu, Real.log_two_gt_d9, Real.log_two_lt_d9])
    (by linarith only [hl, hu, Real.log_two_gt_d9, Real.log_two_lt_d9])

theorem phase_log_eleven_bounds :
    And ((2397895271 / 1000000000 : Real) <= Real.log 11)
      (Real.log 11 <= 2397895275 / 1000000000) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := (5 / 16 : Real)) (by norm_num) 24
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : Real) = 2 ^ (4 : Nat) by norm_num, Real.log_pow]
    norm_num
  rw [show (1 - (5 / 16 : Real)) = 11 / 16 by norm_num,
    Real.log_div (by norm_num) (by norm_num), h16] at h
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  exact And.intro (by linarith only [hl, hu, Real.log_two_gt_d9, Real.log_two_lt_d9])
    (by linarith only [hl, hu, Real.log_two_gt_d9, Real.log_two_lt_d9])

theorem phase_log_two_pi_lower : (459 / 250 : Real) < Real.log (2 * Real.pi) := by
  have hd : 3 / Real.pi <= 150 / 157 := by
    apply compensated_div_upper Real.pi_pos
    linarith only [Real.pi_gt_d2]
  have hh := Real.log_le_sub_one_of_pos
    (div_pos (by norm_num : (0 : Real) < 3) Real.pi_pos)
  rw [Real.log_div (by norm_num) Real.pi_ne_zero] at hh
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero]
  linarith only [hh, hd, Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem phase_log_twenty_three_upper : Real.log 23 < (63 / 20 : Real) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 23 / 24)
  have h24 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
    rw [show (24 : Real) = 2 ^ (3 : Nat) * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [Real.log_div (by norm_num) (by norm_num), h24] at h
  linarith only [h, Real.log_two_lt_d9, Real.log_three_lt_d9]

theorem phase_log_thirty_upper : Real.log 30 <= (34012 / 10000 : Real) := by
  rw [show (30 : Real) = (2 * 3) * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

theorem phase_log_forty_upper : Real.log 40 <= (36889 / 10000 : Real) := by
  rw [show (40 : Real) = 2 ^ (3 : Nat) * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num only
  linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem phase_log_fifty_upper : Real.log 50 <= (39121 / 10000 : Real) := by
  rw [show (50 : Real) = 2 * 5 ^ (2 : Nat) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num only
  linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem phase_log_sixty_upper : Real.log 60 <= (40944 / 10000 : Real) := by
  rw [show (60 : Real) = (2 ^ (2 : Nat) * 3) * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  norm_num only
  linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

theorem compensatedGammaLog_small (q : Real) (hq : 0 <= q) (hQ : q <= 1 / 529) :
    (9 / 10) * compensatedGammaLog q <= 1 / 400 := by
  let z : Real := (121 / 4) * q
  have hz : 0 <= z := by dsimp only [z]; positivity
  have hA : 0 < 1 + (81 / 4 : Real) * q := by linarith only [hq]
  have hB : 0 < 1 + z := by linarith only [hz]
  have hu := Real.log_le_sub_one_of_pos hA
  have hl := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : Real) < 1) hB)
  rw [Real.log_div (by norm_num) hB.ne', Real.log_one, zero_sub] at hl
  have he : (1 - 1 / (1 + z)) - (z - z ^ 2) = z ^ 3 / (1 + z) := by
    field_simp [hB.ne']
    ring
  have hn : 0 <= (1 - 1 / (1 + z)) - (z - z ^ 2) := by
    rw [he]
    positivity
  have hLog : z - z ^ 2 <= Real.log (1 + z) := by linarith only [hl, hn]
  have hprod := mul_nonneg (sub_nonneg.mpr hQ)
    (show 0 <= 1 / 529 + q by linarith only [hq])
  have hq2 : q ^ 2 <= (1 / 529 : Real) ^ 2 := by nlinarith only [hprod]
  dsimp only [z] at hLog
  dsimp only [compensatedGammaLog]
  nlinarith only [hu, hLog, hq2, hQ]

end PrimeFactorOscillations
