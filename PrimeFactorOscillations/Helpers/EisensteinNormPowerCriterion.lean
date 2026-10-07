/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.EisensteinNormCriterion
import PrimeFactorOscillations.Helpers.NicolasPowerPeakSupply

/-!
# Power-saving consequences of the corrected norm profile

An eventual ONE-SIDED bound on the complete corrected profile excludes
zeta zeros to the right of its exponent. The square-root version is
equivalent to RH. No power-saving estimate is assumed proved independently.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Robin1984

theorem nicolasLog_le_of_eisensteinNormPowerDiscrepancy
    (C alpha : Real) (hC : 0 < C)
    (hBound : Filter.Eventually (fun N : Nat =>
      eisensteinNormPowerDiscrepancy N <= C * (N : Real) ^ alpha) atTop) :
    Filter.Eventually (fun N : Nat => nicolasLogMertensOscillation (N : Real) <=
      C * (N : Real) ^ (alpha - 1)) atTop := by
  filter_upwards [hBound, eventually_ge_atTop (3 : Nat),
    tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1] with N hB hN hTheta
  rw [eisensteinNormPowerDiscrepancy_exact N hTheta] at hB
  have hn3 : (3 : Real) <= N := by exact_mod_cast hN
  have hn : (0 : Real) < N := by linarith
  have hlog : 1 <= Real.log (N : Real) :=
    ((Real.lt_log_iff_exp_lt hn).mpr (Real.exp_one_lt_three.trans_le hn3)).le
  by_cases hF : nicolasLogMertensOscillation (N : Real) <= 0
  . exact hF.trans (by positivity)
  . have hF0 : 0 <= nicolasLogMertensOscillation (N : Real) := (lt_of_not_ge hF).le
    have hLow := mul_le_mul_of_nonneg_left hlog
      (mul_nonneg hn.le hF0)
    have hFN : nicolasLogMertensOscillation (N : Real) * N <= C * (N : Real) ^ alpha := by
      nlinarith only [hLow, hB]
    have hCancel : (C * (N : Real) ^ alpha / N) * N = C * (N : Real) ^ alpha := by
      field_simp
    calc
      _ <= C * (N : Real) ^ alpha / N := by nlinarith only [hFN, hCancel, hn]
      _ = _ := by rw [Real.rpow_sub hn, Real.rpow_one]; ring

theorem no_zeta_zero_right_of_eisensteinNormPowerDiscrepancy
    (C alpha : Real) (hC : 0 < C) (hHalf : 1 / 2 <= alpha) (_hAlpha : alpha < 1)
    (hBound : Filter.Eventually (fun N : Nat =>
      eisensteinNormPowerDiscrepancy N <= C * (N : Real) ^ alpha) atTop)
    {rho : Complex} (hRight : alpha < rho.re) (hOne : rho.re < 1) :
    Not (riemannZeta rho = 0) := by
  intro hZero
  let b : Real := ((1 - rho.re) + (1 - alpha)) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbHalf : b <= 1 / 2 := by dsimp [b]; linarith
  have hLower : 1 - rho.re < b := by dsimp [b]; linarith
  have hExponent : alpha - 1 <= -b := by dsimp [b]; linarith
  have hExcursions := nicolasK_integer_power_excursions_of_zero
    hZero (lt_of_le_of_lt hHalf hRight) hOne hLower hbHalf
  choose M hM using eventually_atTop.mp
    (nicolasLog_le_of_eisensteinNormPowerDiscrepancy C alpha hC hBound)
  choose N hN hPeak using nicolasLog_power_unbounded_of_K_integer_excursions
    b hb (by linarith) hExcursions.1 hExcursions.2 C (max M 1)
  have hMN : M <= N := (le_max_left M 1).trans hN
  have hNOne : (1 : Real) <= N := by exact_mod_cast (le_max_right M 1).trans hN
  have hPower := Real.rpow_le_rpow_of_exponent_le hNOne hExponent
  have hUpper := (hM N hMN).trans (mul_le_mul_of_nonneg_left hPower hC.le)
  exact (not_lt_of_ge hUpper) hPeak

theorem riemannHypothesis_iff_eisensteinNormPowerDiscrepancy_sqrt_bound :
    RiemannHypothesis <-> exists C : Real, 0 < C /\
      Filter.Eventually (fun N : Nat =>
        eisensteinNormPowerDiscrepancy N <= C * (N : Real) ^ (1 / 2 : Real)) atTop := by
  constructor
  . intro hRH
    refine Exists.intro 1 (And.intro (by norm_num) ?_)
    filter_upwards [riemannHypothesis_iff_eventually_nicolasLog_nat_neg.mp hRH,
      eventually_ge_atTop (1 : Nat),
      tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1] with N hF hN hTheta
    rw [eisensteinNormPowerDiscrepancy_exact N hTheta]
    have hn1 : (1 : Real) <= N := by exact_mod_cast hN
    have hNonpos := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Nat.cast_nonneg N) (Real.log_nonneg hn1)) hF.le
    exact hNonpos.trans (by positivity)
  . intro h
    choose C hC hBound using h
    by_contra hNot
    choose rho hZero hHalf hOne using
      exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNot
    exact no_zeta_zero_right_of_eisensteinNormPowerDiscrepancy C (1 / 2) hC
      le_rfl (by norm_num) hBound hHalf hOne hZero

end PrimeFactorOscillations
