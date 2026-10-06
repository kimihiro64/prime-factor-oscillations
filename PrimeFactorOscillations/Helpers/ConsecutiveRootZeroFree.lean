/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ConsecutiveRootCriterion
import PrimeFactorOscillations.Helpers.NicolasPowerPeakSupply

/-!
# Power-sized polynomial degree and zeta zeros

The eventual sign of the actual consecutive-root-plus-prime profile, with
degree at most C * N ^ alpha, excludes zeros to the right of alpha.
The sign remains a hypothesis: no new unconditional zero-free strip follows.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Robin1984

theorem eventually_power_bounded_degree_le
    (d : Nat -> Nat) (C alpha : Real) (hAlpha : alpha < 1)
    (hDegree : Filter.Eventually
      (fun N : Nat => (d N : Real) <= C * (N : Real) ^ alpha) atTop) :
    Filter.Eventually (fun N : Nat => d N <= N) atTop := by
  have hDecay : Tendsto (fun N : Nat => C * (N : Real) ^ (alpha - 1))
      atTop (nhds 0) := by
    have h := ((tendsto_rpow_neg_atTop
      (show 0 < 1 - alpha by linarith)).comp tendsto_natCast_atTop_atTop).const_mul C
    simpa only [neg_sub, mul_zero, Function.comp_def] using h
  filter_upwards [hDegree, hDecay.eventually_lt_const (by norm_num : (0 : Real) < 1),
    eventually_ge_atTop (1 : Nat)] with N hD hSmall hN
  have hn : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hPower : (N : Real) ^ (alpha - 1) * N = (N : Real) ^ alpha := by
    calc
      _ = (N : Real) ^ (alpha - 1) * (N : Real) ^ (1 : Real) := by rw [Real.rpow_one]
      _ = (N : Real) ^ ((alpha - 1) + 1) := (Real.rpow_add hn _ _).symm
      _ = _ := by congr 1; ring
  have hMul := mul_lt_mul_of_pos_right hSmall hn
  rw [mul_assoc, hPower, one_mul] at hMul
  exact_mod_cast (hD.trans_lt hMul).le

theorem nicolasLog_le_of_power_degree_signed_profile
    (d : Nat -> Nat) (hd : forall N, 1 <= d N)
    (C alpha : Real) (hAlpha : alpha < 1)
    (hDegree : Filter.Eventually
      (fun N : Nat => (d N : Real) <= C * (N : Real) ^ alpha) atTop)
    (hSign : Filter.Eventually
      (fun N : Nat => (consecutiveRootLaw (d N) (hd N)).logError N 1 <= 0) atTop) :
    Filter.Eventually (fun N : Nat => nicolasLogMertensOscillation (N : Real) <=
      2 * C * (N : Real) ^ (alpha - 1)) atTop := by
  filter_upwards [hDegree, hSign, eventually_power_bounded_degree_le d C alpha hAlpha hDegree,
    eventually_ge_atTop (1 : Nat),
    tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1] with N hD hS hdN hN hTheta
  have hn : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hdReal : (1 : Real) <= d N := by exact_mod_cast hd N
  rw [consecutiveRootLaw_logError_exact (d N) (hd N) N hdN hTheta] at hS
  have hTail := (primeAddedRootTail_bounds N hN ((d N : Real) - 1)
    (by linarith)).2
  have hQ := primeProfileQuadraticTail_bounds N hN
  have hPower : (N : Real) ^ (alpha - 1) * N = (N : Real) ^ alpha := by
    calc
      _ = (N : Real) ^ (alpha - 1) * (N : Real) ^ (1 : Real) := by rw [Real.rpow_one]
      _ = (N : Real) ^ ((alpha - 1) + 1) := (Real.rpow_add hn _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ <= primeAddedRootTail N ((d N : Real) - 1) := by linarith
    _ <= ((d N : Real) - 1) * primeProfileQuadraticTail N := hTail
    _ <= (d N : Real) * (2 / (N : Real)) :=
      mul_le_mul (by linarith) hQ.2 hQ.1 (by positivity)
    _ <= (C * (N : Real) ^ alpha) * (2 / (N : Real)) :=
      mul_le_mul_of_nonneg_right hD (by positivity)
    _ = _ := by rw [<- hPower]; field_simp

/-- The family hypothesis is the full profile sign, not a zero-free assumption. -/
theorem no_zeta_zero_right_of_power_degree_signed_profile
    (d : Nat -> Nat) (hd : forall N, 1 <= d N)
    (C alpha : Real) (hC : 0 < C) (hHalf : 1 / 2 <= alpha) (hAlpha : alpha < 1)
    (hDegree : Filter.Eventually
      (fun N : Nat => (d N : Real) <= C * (N : Real) ^ alpha) atTop)
    (hSign : Filter.Eventually
      (fun N : Nat => (consecutiveRootLaw (d N) (hd N)).logError N 1 <= 0) atTop)
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
    (nicolasLog_le_of_power_degree_signed_profile d hd C alpha hAlpha hDegree hSign)
  choose N hN hPeak using nicolasLog_power_unbounded_of_K_integer_excursions
    b hb (by linarith) hExcursions.1 hExcursions.2 (2 * C) (max M 1)
  have hMN : M <= N := (le_max_left M 1).trans hN
  have hNOne : (1 : Real) <= N := by exact_mod_cast (le_max_right M 1).trans hN
  have hPower := Real.rpow_le_rpow_of_exponent_le hNOne hExponent
  have hBound := (hM N hMN).trans
    (mul_le_mul_of_nonneg_left hPower (by positivity : 0 <= 2 * C))
  exact (not_lt_of_ge hBound) hPeak

theorem riemannHypothesis_of_sqrt_degree_signed_profile
    (d : Nat -> Nat) (hd : forall N, 1 <= d N) (C : Real) (hC : 0 < C)
    (hDegree : Filter.Eventually
      (fun N : Nat => (d N : Real) <= C * (N : Real) ^ (1 / 2 : Real)) atTop)
    (hSign : Filter.Eventually
      (fun N : Nat => (consecutiveRootLaw (d N) (hd N)).logError N 1 <= 0) atTop) :
    RiemannHypothesis := by
  by_contra hNot
  choose rho hZero hHalf hOne using
    exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNot
  exact no_zeta_zero_right_of_power_degree_signed_profile d hd C (1 / 2) hC
    le_rfl (by norm_num) hDegree hSign hHalf hOne hZero

end PrimeFactorOscillations
