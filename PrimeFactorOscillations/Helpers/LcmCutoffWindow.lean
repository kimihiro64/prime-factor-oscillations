/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LcmStripWindow

/-!
# The seven-eighths modified-LCM window with the literal cutoff logarithm

A slightly wider intermediate height-based window absorbs the difference
between log N and log(log(M_N)). The final endpoint is exactly
9/8 + 4/log N, and the complete signed margin remains 1/200.

The intermediate coefficient is 401/100. Its positive prime-tail supply
still exceeds the spectral allowance by more than 1/200. Every theorem
requiring the seven-eighths zero-free region retains that hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Filter Asymptotics Robin1984

theorem lcmStripWindowLimit_seven_eighths_reserve :
    (1 / 200 : Real) <
      lcmStripWindowLimit (7 / 8) (401 / 100) ((12 / 11 : Real) ^ 8) 24 := by
  let C := lcmStripFiniteTailCoefficient (7 / 8) ((12 / 11 : Real) ^ 8) 24
  let beta := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  have hLoss := lcmStrip_seven_eighths_loss_lt beta
    robin_zero_constant_le_one_twentieth
  have hRoot : Real.sqrt ((7 / 8 : Real) * (1 - 7 / 8)) = Real.sqrt 7 / 8 := by
    have h64 : Real.sqrt (64 : Real) = 8 := by
      rw [show (64 : Real) = 8 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : Real) <= 8)]
    rw [show (7 / 8 : Real) * (1 - 7 / 8) = 7 / 64 by norm_num,
      Real.sqrt_div (by norm_num : (0 : Real) <= 7), h64]
  have hCoeff : (9 / 8 : Real) * lcmStripSpectralConstant (7 / 8) =
      9 * beta / (2 * Real.sqrt 7) := by
    unfold lcmStripSpectralConstant
    rw [hRoot]
    dsimp only [beta]
    ring
  have hMaxLoss : (9 / 8 : Real) * max (lcmStripSpectralConstant (7 / 8)) 0 <
      (3 / 35 : Real) := by
    by_cases h : 0 <= lcmStripSpectralConstant (7 / 8)
    . rw [max_eq_left h, hCoeff]
      exact hLoss
    . rw [max_eq_right (le_of_not_ge h), mul_zero]
      norm_num
  have hExp : (99 / 100 : Real) <= Real.exp (-(1 / 100 : Real)) := by
    have h := Real.add_one_le_exp (-(1 / 100 : Real))
    linarith only [h]
  have hSupply : (1376 / 14641 : Real) < C * Real.exp (-4) :=
    lcmStrip_seven_eighths_supply_gt
  have hPos : 0 <= C * Real.exp (-4) := by linarith only [hSupply]
  have hCredit :
      (1376 / 14641 : Real) * (99 / 100) < C * Real.exp (-(401 / 100 : Real)) := by
    calc
      _ < (C * Real.exp (-4)) * (99 / 100) :=
        mul_lt_mul_of_pos_right hSupply (by norm_num)
      _ <= (C * Real.exp (-4)) * Real.exp (-(1 / 100 : Real)) :=
        mul_le_mul_of_nonneg_left hExp hPos
      _ = _ := by
        rw [mul_assoc, <- Real.exp_add]
        congr 1
        norm_num
  unfold lcmStripWindowLimit
  rw [show (2 : Real) - 7 / 8 = 9 / 8 by norm_num]
  change (1 / 200 : Real) <
    C * Real.exp (-(401 / 100 : Real)) -
      (9 / 8 : Real) * max (lcmStripSpectralConstant (7 / 8)) 0
  linarith only [hCredit, hMaxLoss]

theorem eventually_cutoff_seven_eighths_le_height_window :
    Filter.Eventually (fun N : Nat =>
      (9 / 8 : Real) + 4 / Real.log (N : Real) <=
        lcmStripMovingExponent (7 / 8) (401 / 100) N) atTop := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hHeight : Tendsto (fun N : Nat => Real.log (modifiedLcm N : Real)) atTop atTop :=
    modifiedLcm_log_isEquivalent_id.symm.tendsto_atTop hn
  have hLogEq := modifiedLcm_log_isEquivalent_id.log hn
  have hRatio := (isEquivalent_iff_tendsto_one
    ((Real.tendsto_log_atTop.comp hHeight).eventually_ne_atTop 0)).mp hLogEq.symm
  have hNear := hRatio.eventually_const_lt (by norm_num : (400 / 401 : Real) < 1)
  filter_upwards [hNear, eventually_ge_atTop (8 : Nat)] with N hR hN
  have hNat : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hLog := Real.log_pos hNat
  have hLogNe := hLog.ne'
  have hScaled := mul_lt_mul_of_pos_left hR (by norm_num : (0 : Real) < 401 / 100)
  simp only [Pi.div_apply, Function.comp_def] at hScaled
  have hScaled' : (4 : Real) <
      ((401 / 100) / Real.log (Real.log (modifiedLcm N : Real))) * Real.log (N : Real) := by
    convert hScaled using 1 <;> ring
  have hCancel : ((4 : Real) / Real.log (N : Real)) * Real.log (N : Real) = 4 := by
    field_simp [hLogNe]
  have hCompare :
      4 / Real.log (N : Real) <
        (401 / 100) / Real.log (Real.log (modifiedLcm N : Real)) := by
    by_contra hNot
    have hUpper := mul_le_mul_of_nonneg_right (le_of_not_gt hNot) hLog.le
    rw [hCancel] at hUpper
    exact (not_lt_of_ge hUpper) hScaled'
  unfold lcmStripMovingExponent lcmMovingExponent
  linarith only [hCompare]

theorem eventually_modifiedLcm_seven_eighths_cutoff_scaled
    (hZeroFree : forall s : Complex, (7 / 8 : Real) < s.re -> Not (s = 1) ->
      Not (riemannZeta s = 0)) :
    Filter.Eventually (fun N : Nat => forall k : Real, forall hk : 1 < k,
      k <= (9 / 8 : Real) + 4 / Real.log (N : Real) ->
        (1 / 200 : Real) <
          Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) *
            (N : Real) ^ (1 / 8 : Real) * Real.log (N : Real)) atTop := by
  have hWindow := eventually_modifiedLcm_strip_window_scaled
    (7 / 8) (401 / 100) ((12 / 11 : Real) ^ 8) (1 / 200) 24
    (by norm_num) (by norm_num) (by norm_num) hZeroFree
    lcmStripWindowLimit_seven_eighths_reserve
  norm_num only [show (1 : Real) - 7 / 8 = 1 / 8 by norm_num] at hWindow
  filter_upwards [hWindow, eventually_cutoff_seven_eighths_le_height_window]
    with N hW hComparison
  intro k hk hLe
  exact hW k hk (hLe.trans hComparison)

theorem eventually_modifiedLcm_seven_eighths_cutoff
    (hZeroFree : forall s : Complex, (7 / 8 : Real) < s.re -> Not (s = 1) ->
      Not (riemannZeta s = 0)) :
    Filter.Eventually (fun N : Nat => forall k : Real, forall hk : 1 < k,
      k <= (9 / 8 : Real) + 4 / Real.log (N : Real) ->
        1 / (200 * (N : Real) ^ (1 / 8 : Real) * Real.log (N : Real)) <
          Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N))) atTop := by
  filter_upwards [eventually_modifiedLcm_seven_eighths_cutoff_scaled hZeroFree,
    eventually_ge_atTop (8 : Nat)] with N hWindow hN
  intro k hk hLe
  have hNat : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hPow : 0 < (N : Real) ^ (1 / 8 : Real) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hNat) _
  have hLog := Real.log_pos hNat
  have hS : 0 < (N : Real) ^ (1 / 8 : Real) * Real.log (N : Real) :=
    mul_pos hPow hLog
  have hCancel :
      (1 / (200 * (N : Real) ^ (1 / 8 : Real) * Real.log (N : Real))) *
        ((N : Real) ^ (1 / 8 : Real) * Real.log (N : Real)) = (1 / 200 : Real) := by
    field_simp [hPow.ne', hLog.ne']
  by_contra hNot
  have hUpper := mul_le_mul_of_nonneg_right (le_of_not_gt hNot) hS.le
  rw [hCancel] at hUpper
  have hScaled := hWindow k hk hLe
  rw [mul_assoc] at hScaled
  exact (not_lt_of_ge hUpper) hScaled

end PrimeFactorOscillations
