/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ModifiedLcmHeight

/-!
# The actual nonlinear height correction

Transfer the proved logarithmic-height increment through the two logarithms
of the generalized Robin normalizer, using exact two-sided inequalities.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Asymptotics

theorem lcm_log_sub_log_bounds (a b : Real) (hb : 0 < b) (hba : b <= a) :
    (a - b) / a <= Real.log a - Real.log b /\
      Real.log a - Real.log b <= (a - b) / b := by
  have ha : 0 < a := hb.trans_le hba
  have hRatio : 0 < a / b := div_pos ha hb
  refine And.intro ?_ ?_
  . calc
      _ = 1 - Inv.inv (a / b) := by field_simp [ha.ne', hb.ne']
      _ <= Real.log (a / b) := Real.one_sub_inv_le_log_of_pos hRatio
      _ = _ := Real.log_div ha.ne' hb.ne'
  . calc
      _ = Real.log (a / b) := (Real.log_div ha.ne' hb.ne').symm
      _ <= a / b - 1 := Real.log_le_sub_one_of_pos hRatio
      _ = _ := by field_simp [hb.ne']

theorem lcm_loglog_increment_bounds (a b : Real) (hb : 1 < b) (hba : b <= a) :
    (a - b) / (a * Real.log a) <= Real.log (Real.log a) - Real.log (Real.log b) /\
      Real.log (Real.log a) - Real.log (Real.log b) <= (a - b) / (b * Real.log b) := by
  have hbPos : 0 < b := lt_trans (by norm_num) hb
  have haOne : 1 < a := hb.trans_le hba
  have hInner := lcm_log_sub_log_bounds a b hbPos hba
  have hOuter := lcm_log_sub_log_bounds (Real.log a) (Real.log b)
    (Real.log_pos hb) (Real.log_le_log hbPos hba)
  refine And.intro ?_ ?_
  . have hFirst := div_le_div_of_nonneg_right hInner.1 (Real.log_pos haOne).le
    simpa only [div_div] using hFirst.trans hOuter.1
  . have hLast := div_le_div_of_nonneg_right hInner.2 (Real.log_pos hb).le
    simpa only [div_div] using hOuter.2.trans hLast

theorem modifiedLcm_theta_le_log (N : Nat) :
    Chebyshev.theta (N : Real) <= Real.log (modifiedLcm N : Real) := by
  rw [modifiedLcm_log_identity]
  have hPsi := Chebyshev.theta_le_psi (N : Real)
  have hSum : 0 <= (modifiedLcmRaisedPrimes N).sum (fun p => Real.log (p : Real)) := by
    apply Finset.sum_nonneg
    intro p hp
    apply Real.log_nonneg
    exact_mod_cast (mem_modifiedLcmRaisedPrimes N p |>.mp hp).1.one_le
  linarith only [hPsi, hSum]

theorem tendsto_modifiedLcm_log_div_self :
    Tendsto (fun N : Nat => Real.log (modifiedLcm N : Real) / (N : Real))
      atTop (nhds (1 : Real)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsqrt := Real.tendsto_sqrt_atTop.comp hn
  have hProduct := tendsto_modifiedLcm_log_height.mul hsqrt.inv_tendsto_atTop
  have h := hProduct.add tendsto_primeProfile_theta_ratio
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  calc
    _ = (Real.log (modifiedLcm N : Real) - Chebyshev.theta (N : Real)) /
        (Real.sqrt (N : Real) * Real.sqrt (N : Real)) +
          Chebyshev.theta (N : Real) / (N : Real) := by
      simp only [Function.comp_def, Pi.inv_apply, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg N)]; ring

theorem modifiedLcm_log_isEquivalent_id :
    Asymptotics.IsEquivalent atTop
      (fun N : Nat => Real.log (modifiedLcm N : Real)) (fun N : Nat => (N : Real)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  exact (Asymptotics.isEquivalent_iff_tendsto_one (hn.eventually_ne_atTop 0)).mpr
    tendsto_modifiedLcm_log_div_self

theorem lcm_scaled_loglog_bound_identity (a b x : Real) (hx : 0 < x) :
    (a - b) / (a * Real.log a) * Real.sqrt x * Real.log x =
      ((a - b) / Real.sqrt x) * (x / a) * (Real.log x / Real.log a) := by
  have hQuot : x / Real.sqrt x = Real.sqrt x := by
    apply (div_eq_iff (Real.sqrt_pos.mpr hx).ne').mpr
    exact (Real.mul_self_sqrt hx.le).symm
  have hInv : x * Inv.inv (Real.sqrt x) = Real.sqrt x := by
    simpa only [div_eq_mul_inv] using hQuot
  calc
    _ = (a - b) * (x * Inv.inv (Real.sqrt x)) *
        Inv.inv a * (Real.log x * Inv.inv (Real.log a)) := by
      rw [hInv]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by simp only [div_eq_mul_inv]; ring

def modifiedLcmHeightCorrection (N : Nat) : Real :=
  Real.log (Real.log (Real.log (modifiedLcm N : Real))) -
    Real.log (Real.log (Chebyshev.theta (N : Real)))

theorem modifiedLcmHeightCorrection_bounds (N : Nat)
    (hTheta : 1 < Chebyshev.theta (N : Real)) :
    (Real.log (modifiedLcm N : Real) - Chebyshev.theta (N : Real)) /
        (Real.log (modifiedLcm N : Real) * Real.log (Real.log (modifiedLcm N : Real))) <=
      modifiedLcmHeightCorrection N /\
    modifiedLcmHeightCorrection N <=
      (Real.log (modifiedLcm N : Real) - Chebyshev.theta (N : Real)) /
        (Chebyshev.theta (N : Real) * Real.log (Chebyshev.theta (N : Real))) :=
  lcm_loglog_increment_bounds _ _ hTheta (modifiedLcm_theta_le_log N)

theorem tendsto_modifiedLcm_scaled_height_bound
    (a : Nat -> Real)
    (hEq : Asymptotics.IsEquivalent atTop a (fun N : Nat => (N : Real))) :
    Tendsto (fun N : Nat =>
      (Real.log (modifiedLcm N : Real) - Chebyshev.theta (N : Real)) /
        (a N * Real.log (a N)) * Real.sqrt (N : Real) * Real.log (N : Real))
      atTop (nhds (Real.sqrt 2)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have ha : Tendsto a atTop atTop := hEq.symm.tendsto_atTop hn
  have hRatio := (Asymptotics.isEquivalent_iff_tendsto_one
    (ha.eventually_ne_atTop 0)).mp hEq.symm
  have hLogEq := hEq.log hn
  have hLogA := Real.tendsto_log_atTop.comp ha
  have hLogRatio := (Asymptotics.isEquivalent_iff_tendsto_one
    (hLogA.eventually_ne_atTop 0)).mp hLogEq.symm
  have h := (tendsto_modifiedLcm_log_height.mul hRatio).mul hLogRatio
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  have hNPos : (0 : Real) < N := by exact_mod_cast hN
  have hIdentity := lcm_scaled_loglog_bound_identity (a N)
    (a N - (Real.log (modifiedLcm N : Real) - Chebyshev.theta (N : Real)))
    (N : Real) hNPos
  have hCancel : a N - (a N - (Real.log (modifiedLcm N : Real) -
      Chebyshev.theta (N : Real))) =
        Real.log (modifiedLcm N : Real) - Chebyshev.theta (N : Real) := by ring
  rw [hCancel] at hIdentity
  exact hIdentity.symm

theorem tendsto_modifiedLcm_heightCorrection_scaled :
    Tendsto (fun N : Nat => modifiedLcmHeightCorrection N *
      Real.sqrt (N : Real) * Real.log (N : Real))
      atTop (nhds (Real.sqrt 2)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLower := tendsto_modifiedLcm_scaled_height_bound
    (fun N : Nat => Real.log (modifiedLcm N : Real)) modifiedLcm_log_isEquivalent_id
  have hUpper := tendsto_modifiedLcm_scaled_height_bound
    (fun N : Nat => Chebyshev.theta (N : Real))
    (primeProfile_theta_isEquivalent_id.comp_tendsto hn)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper
  . filter_upwards [tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1,
      eventually_ge_atTop (1 : Nat)] with N hTheta hN
    have hLog : 0 <= Real.log (N : Real) := Real.log_nonneg (by exact_mod_cast hN)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (modifiedLcmHeightCorrection_bounds N hTheta).1
        (Real.sqrt_nonneg _)) hLog
  . filter_upwards [tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1,
      eventually_ge_atTop (1 : Nat)] with N hTheta hN
    have hLog : 0 <= Real.log (N : Real) := Real.log_nonneg (by exact_mod_cast hN)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (modifiedLcmHeightCorrection_bounds N hTheta).2
        (Real.sqrt_nonneg _)) hLog

end PrimeFactorOscillations
