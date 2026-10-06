/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LcmFiniteTailLower

/-!
# Real prime-square tails and the modified-LCM moving exponent

The finite positive comparison uses real thresholds. Transfer the existing
natural-cutoff PNT exactly, then track the actual loglog(M_N) exponent.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Asymptotics

theorem lcmRealSquareTail_eq_nat_floor (x : Real) (hx : 0 <= x) :
    lcmRealSquareTail x = primeReciprocalSquareTail (Nat.floor x) := by
  have hPred : {p : Nat.Primes | x < (p.val : Real)} =
      {p : Nat.Primes | (Nat.floor x : Real) < (p.val : Real)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Nat.cast_lt]
    exact (Nat.floor_lt hx).symm
  rw [<- lcmRealSquareTail_nat]
  unfold lcmRealSquareTail lcmSquareTailIndicator
  rw [hPred]

theorem tendsto_lcmRealSquareTail_scaled :
    Tendsto (fun x : Real => lcmRealSquareTail x * (x * Real.log x))
      atTop (nhds (1 : Real)) := by
  have hFloor : Tendsto (fun x : Real => Nat.floor x) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b : Real)] with x hx
    exact (Nat.le_floor_iff ((Nat.cast_nonneg b).trans hx)).mpr hx
  have hFloorReal : Tendsto (fun x : Real => (Nat.floor x : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hFloor
  have hInv : Tendsto (fun x : Real => 1 / x) atTop (nhds (0 : Real)) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : Real => Inv.inv x) atTop (nhds 0))
  have hGap : Tendsto (fun x : Real => 1 - (Nat.floor x : Real) / x)
      atTop (nhds (0 : Real)) := by
    apply squeeze_zero' ?_ ?_ hInv
    . filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
      have h := div_le_div_of_nonneg_right (Nat.floor_le hx.le) hx.le
      rw [div_self hx.ne'] at h
      linarith
    . filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
      have h := div_le_div_of_nonneg_right (Nat.lt_floor_add_one x).le hx.le
      rw [div_self hx.ne', add_div] at h
      linarith
  have hRatio : Tendsto (fun x : Real => (Nat.floor x : Real) / x) atTop (nhds (1 : Real)) := by
    have h := (tendsto_const_nhds (x := (1 : Real))).sub hGap
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [] with x
    ring
  have hEq : IsEquivalent atTop (fun x : Real => (Nat.floor x : Real)) (fun x : Real => x) :=
    (isEquivalent_iff_tendsto_one (eventually_ne_atTop (0 : Real))).mpr hRatio
  have hReverse := (isEquivalent_iff_tendsto_one
    (hFloorReal.eventually_ne_atTop 0)).mp hEq.symm
  have hLogEq := hEq.log (tendsto_id : Tendsto (fun x : Real => x) atTop atTop)
  have hLogReverse := (isEquivalent_iff_tendsto_one
    ((Real.tendsto_log_atTop.comp hFloorReal).eventually_ne_atTop 0)).mp hLogEq.symm
  have hTail := tendsto_primeReciprocalSquareTail_scaled.comp hFloor
  have h := (hTail.mul hReverse).mul hLogReverse
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  have hx0 : 0 <= x := by linarith
  have hFloorTwo : 2 <= Nat.floor x := (Nat.le_floor_iff hx0).mpr (by exact_mod_cast hx)
  have hFloorPos : (0 : Real) < (Nat.floor x : Real) := by
    exact_mod_cast (show 0 < Nat.floor x by omega)
  have hFloorOne : (1 : Real) < (Nat.floor x : Real) := by
    exact_mod_cast (show 1 < Nat.floor x by omega)
  have hLogFloor := (Real.log_pos hFloorOne).ne'
  simp only [Function.comp_def, Pi.div_apply]
  rw [lcmRealSquareTail_eq_nat_floor x hx0]
  field_simp [hFloorPos.ne', hLogFloor]

theorem tendsto_lcmRealSquareTail_dilated (a : Real) (ha : 0 < a) :
    Tendsto (fun N : Nat => lcmRealSquareTail (a * (N : Real)) *
      (a * (N : Real) * Real.log (a * (N : Real)))) atTop (nhds (1 : Real)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hScale : Tendsto (fun N : Nat => a * (N : Real)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hn.eventually_ge_atTop (b / a)] with N hN
    calc
      b = a * (b / a) := by field_simp [ha.ne']
      _ <= a * (N : Real) := mul_le_mul_of_nonneg_left hN ha.le
  exact tendsto_lcmRealSquareTail_scaled.comp hScale

theorem tendsto_lcm_log_dilation_ratio (a : Real) (ha : 0 < a) :
    Tendsto (fun N : Nat => Real.log (N : Real) / Real.log (a * (N : Real)))
      atTop (nhds (1 : Real)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hInvLog := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hn)
  have hSmall := hInvLog.const_mul (Real.log a)
  simp only [mul_zero] at hSmall
  have hRatio : Tendsto (fun N : Nat => Real.log (a * (N : Real)) / Real.log (N : Real))
      atTop (nhds (1 : Real)) := by
    have h := (tendsto_const_nhds (x := (1 : Real))).add hSmall
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : Nat)] with N hN
    have hNPos : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
    have hLog : Not (Real.log (N : Real) = 0) :=
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    simp only [Function.comp_def]
    rw [Real.log_mul ha.ne' hNPos.ne']
    field_simp [hLog]
    ring
  have h := (tendsto_const_nhds (x := (1 : Real))).div hRatio (by norm_num)
  change Tendsto (fun N : Nat => 1 / (Real.log (a * (N : Real)) / Real.log (N : Real)))
    atTop (nhds ((1 : Real) / 1)) at h
  simpa only [one_div, inv_div, inv_one] using h

def lcmMovingExponent (c : Real) (N : Nat) : Real :=
  3 / 2 + c / Real.log (Real.log (modifiedLcm N : Real))

theorem tendsto_lcmMovingExponent (c : Real) :
    Tendsto (lcmMovingExponent c) atTop (nhds (3 / 2 : Real)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hHeight : Tendsto (fun N : Nat => Real.log (modifiedLcm N : Real)) atTop atTop :=
    modifiedLcm_log_isEquivalent_id.symm.tendsto_atTop hn
  have hInv := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hHeight)
  have h := (tendsto_const_nhds (x := (3 / 2 : Real))).add (hInv.const_mul c)
  change Tendsto (fun N : Nat => 3 / 2 + c / Real.log (Real.log (modifiedLcm N : Real)))
    atTop (nhds (3 / 2 : Real))
  simpa only [Function.comp_def, div_eq_mul_inv, mul_zero, add_zero] using h

theorem tendsto_lcmMovingExponent_power_scale (c : Real) :
    Tendsto (fun N : Nat => (N : Real) ^ (3 / 2 - lcmMovingExponent c N))
      atTop (nhds (Real.exp (-c))) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hHeight : Tendsto (fun N : Nat => Real.log (modifiedLcm N : Real)) atTop atTop :=
    modifiedLcm_log_isEquivalent_id.symm.tendsto_atTop hn
  have hLogEq := modifiedLcm_log_isEquivalent_id.log hn
  have hRatio := (isEquivalent_iff_tendsto_one
    ((Real.tendsto_log_atTop.comp hHeight).eventually_ne_atTop 0)).mp hLogEq.symm
  have hLinear := hRatio.const_mul (-c)
  simp only [mul_one] at hLinear
  have h := (Real.continuous_exp.tendsto (-c)).comp hLinear
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with N hN
  have hx : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Real.rpow_def_of_pos hx]
  simp only [lcmMovingExponent, Pi.div_apply, Function.comp_def]
  congr 1
  ring

theorem tendsto_lcmMovingExponent_fixed_power (a c : Real) (ha : 0 < a) :
    Tendsto (fun N : Nat => a ^ (2 - lcmMovingExponent c N))
      atTop (nhds (a ^ (1 / 2 : Real))) := by
  have hExponent := (tendsto_const_nhds (x := (2 : Real))).sub (tendsto_lcmMovingExponent c)
  norm_num only [show (2 : Real) - 3 / 2 = 1 / 2 by norm_num] at hExponent
  have hLinear := hExponent.const_mul (Real.log a)
  have h := (Real.continuous_exp.tendsto (Real.log a * (1 / 2 : Real))).comp hLinear
  simpa only [Real.rpow_def_of_pos ha, Function.comp_def] using h

end PrimeFactorOscillations
