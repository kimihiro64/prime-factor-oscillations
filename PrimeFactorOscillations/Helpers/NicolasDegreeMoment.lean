/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasSpectralPsi

/-!
# A stronger degree bound for the actual zero coefficient

The audited three-halves zero moment changes the degree factor in the
weighted psi estimate from n to sqrt(n). Its consumer is a pointwise
power-saving bound sufficient for the nonlinear Nicolas endpoint correction.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Robin1984

def nicolasThreeHalfZeroWeight (p : RiemannXiDivisorZeroIndex) : Real :=
  Inv.inv (norm (riemannXiDivisorZeroValue p) * Real.sqrt (norm (riemannXiDivisorZeroValue p)))

theorem summable_nicolasThreeHalfZeroWeight : Summable nicolasThreeHalfZeroWeight := by
  apply (summable_riemannXiDivisorZero_norm_inv_rpow (a := (3 / 2 : Real)) (by norm_num)).congr
  intro p
  have ha : 0 < norm (riemannXiDivisorZeroValue p) :=
    norm_pos_iff.mpr (riemannXiDivisorZeroValue_ne_zero p)
  rw [show (3 / 2 : Real) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (inv_pos.mpr ha), Real.rpow_one, <- Real.sqrt_eq_rpow, Real.sqrt_inv]
  dsimp [nicolasThreeHalfZeroWeight]
  rw [mul_inv_rev]
  ring

def nicolasThreeHalfZeroConstant : Real := tsum nicolasThreeHalfZeroWeight

theorem norm_nicolasZeroCoefficient_le_sqrt_degree (hRH : RiemannHypothesis)
    {n : Nat} (hn : 2 <= n) (p : RiemannXiDivisorZeroIndex) :
    norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
        riemannXiDivisorZeroValue p) <=
      2 * Real.sqrt (n : Real) * nicolasThreeHalfZeroWeight p := by
  let rho := riemannXiDivisorZeroValue p
  let a : Real := norm rho
  let b : Real := norm ((n : Complex) - rho)
  have hN : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := norm_pos_iff.mpr (riemannXiDivisorZeroValue_ne_zero p)
  have hRe : rho.re = (1 / 2 : Real) :=
    riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
  have hab : a <= b := by
    have h := norm_le_norm_sub_nat_of_re_eq_half (n := n) (by omega) hRe
    dsimp [a, b]
    exact h.trans_eq (norm_sub_rev _ _)
  have hbN : (n : Real) / 2 <= b := by
    have hnReal : (2 : Real) <= n := by exact_mod_cast hn
    have h := Complex.re_le_norm ((n : Complex) - rho)
    simp only [Complex.sub_re, Complex.natCast_re, hRe] at h
    dsimp [b]
    linarith only [h, hnReal]
  have hb : 0 < b := (div_pos hN (by norm_num)).trans_le hbN
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hprod : a * ((n : Real) / 2) <= b * b :=
    mul_le_mul hab hbN (by positivity) hb.le
  have hmul := mul_le_mul_of_nonneg_left hprod (show 0 <= 4 * (n : Real) by positivity)
  have hsquares : ((n : Real) * Real.sqrt a) ^ 2 <=
      (2 * Real.sqrt (n : Real) * b) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hN.le]
    nlinarith only [hmul, mul_nonneg ha.le (sq_nonneg (n : Real))]
  have hsquare_mono (u v : Real) (hu : 0 <= u) (hv : 0 <= v) (h : u ^ 2 <= v ^ 2) :
      u <= v := by nlinarith only [hu, hv, h]
  have hnum : (n : Real) * Real.sqrt a <= 2 * Real.sqrt (n : Real) * b :=
    hsquare_mono _ _ (by positivity) (by positivity) hsquares
  have hreal : (n : Real) / (a * b) <= 2 * Real.sqrt (n : Real) / (a * Real.sqrt a) := by
    have h := mul_le_mul_of_nonneg_right hnum
      (show 0 <= Inv.inv (a * b * Real.sqrt a) by positivity)
    convert h using 1
    . field_simp [ha.ne', hb.ne', hsa.ne']
    . field_simp [ha.ne', hb.ne', hsa.ne']
  rw [norm_div, norm_div]
  norm_num only [Complex.norm_natCast]
  change (n : Real) / b / a <= 2 * Real.sqrt (n : Real) * nicolasThreeHalfZeroWeight p
  calc
    _ = (n : Real) / (a * b) := by ring
    _ <= 2 * Real.sqrt (n : Real) / (a * Real.sqrt a) := hreal
    _ = _ := by
      dsimp [nicolasThreeHalfZeroWeight, a, rho]
      rw [div_eq_mul_inv]


theorem nicolasDegreeRemainderScalar_le
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) (hL : 1 <= Real.log x) :
    x ^ ((1 / 2 : Real) - n) * Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 * ((-x ^ ((1 / 2 : Real) - n) / ((1 / 2 : Real) - n)) *
          Inv.inv ((Real.log x) ^ (3 : Nat))) <=
      5 * (x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x)) := by
  have hX : 0 <= x ^ ((1 / 2 : Real) - n) := Real.rpow_nonneg (by linarith) _
  have hLog : 0 < Real.log x := Real.log_pos hx
  have hu0 : 0 <= Inv.inv (Real.log x) := inv_nonneg.mpr hLog.le
  have hu1 : Inv.inv (Real.log x) <= 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hL
  have hu2 : (Inv.inv (Real.log x)) ^ 2 <= Inv.inv (Real.log x) := by
    nlinarith only [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have hu3 : (Inv.inv (Real.log x)) ^ 3 <= Inv.inv (Real.log x) := by
    calc
      _ <= (Inv.inv (Real.log x)) ^ 2 := by
        simpa only [pow_succ, mul_one] using mul_le_mul_of_nonneg_left hu1
          (sq_nonneg (Inv.inv (Real.log x)))
      _ <= _ := hu2
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hd : (1 / 2 : Real) <= (n : Real) - 1 / 2 := by linarith
  have hdInv : Inv.inv ((n : Real) - 1 / 2) <= 2 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1 / 2) hd
  have hfrac : -x ^ ((1 / 2 : Real) - n) / ((1 / 2 : Real) - n) <=
      2 * x ^ ((1 / 2 : Real) - n) := by
    calc
      _ = x ^ ((1 / 2 : Real) - n) / ((n : Real) - 1 / 2) := by
        rw [show (1 / 2 : Real) - n = -((n : Real) - 1 / 2) by ring]
        simp only [neg_div_neg_eq]
      _ <= x ^ ((1 / 2 : Real) - n) * 2 := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hdInv hX
      _ = _ := by ring
  rw [<- inv_pow, <- inv_pow]
  have hsecond := mul_le_mul_of_nonneg_right hfrac (pow_nonneg hu0 3)
  have hsq := mul_le_mul_of_nonneg_left hu2 hX
  have hcube := mul_le_mul_of_nonneg_left hu3 hX
  nlinarith only [hsecond, hsq, hcube]

theorem norm_nicolasDegreeZeroKernel_le (hRH : RiemannHypothesis)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) (hL : 1 <= Real.log x)
    (p : RiemannXiDivisorZeroIndex) :
    norm (robinZeroKernel n (riemannXiDivisorZeroValue p) x /
        riemannXiDivisorZeroValue p) <=
      (2 * Real.sqrt (n : Real) * nicolasThreeHalfZeroWeight p +
        5 * (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) *
      (x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x)) := by
  let rho := riemannXiDivisorZeroValue p
  have hRe : rho.re = (1 / 2 : Real) :=
    riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hReLt : rho.re < n := by rw [hRe]; linarith
  have hF : 0 <= x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x) := by positivity
  have hNorm :
      norm ((x : Complex) ^ (rho - (n : Complex)) *
        ((Inv.inv (Real.log x) : Real) : Complex)) =
      x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x),
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.log_pos hx))]
    simp only [Complex.sub_re, Complex.natCast_re, hRe]
  have hMain := mul_le_mul_of_nonneg_right
    (norm_nicolasZeroCoefficient_le_sqrt_degree hRH hn p) hF
  have hRem := norm_robinZeroKernelRemainder_div_rho_le (by omega : 1 <= n)
    (riemannXiDivisorZeroValue_ne_zero p) hRe hx
  have hRemScalar := mul_le_mul_of_nonneg_left (nicolasDegreeRemainderScalar_le hn hx hL)
    (sq_nonneg (Inv.inv (norm rho)))
  change norm (robinZeroKernel n rho x / rho) <= _
  rw [robinZeroKernel_eq_main_add_remainder (by omega) hx hReLt, add_div]
  have hRewrite :
      ((n : Complex) / ((n : Complex) - rho) *
        (x : Complex) ^ (rho - (n : Complex)) *
          ((Inv.inv (Real.log x) : Real) : Complex)) / rho =
      (((n : Complex) / ((n : Complex) - rho)) / rho) *
        ((x : Complex) ^ (rho - (n : Complex)) *
          ((Inv.inv (Real.log x) : Real) : Complex)) := by ring
  rw [hRewrite]
  have hTriangle := norm_add_le
    ((((n : Complex) / ((n : Complex) - rho)) / rho) *
      ((x : Complex) ^ (rho - (n : Complex)) *
        ((Inv.inv (Real.log x) : Real) : Complex)))
    (robinZeroKernelRemainder n rho x / rho)
  rw [norm_mul, hNorm] at hTriangle
  dsimp only [rho] at hTriangle hRemScalar
  nlinarith only [hTriangle, hMain, hRem, hRemScalar]

theorem norm_tsum_nicolasDegreeZeroKernel_le (hRH : RiemannHypothesis)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) (hL : 1 <= Real.log x) :
    norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
      robinZeroKernel n (riemannXiDivisorZeroValue p) x /
        riemannXiDivisorZeroValue p)) <=
      (2 * Real.sqrt (n : Real) * nicolasThreeHalfZeroConstant +
        5 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))) *
      (x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x)) := by
  let F := x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x)
  have hSeries := summable_robinZeroKernel_div_rho hRH (by omega : 1 <= n) hx
  have hMajor :=
    ((summable_nicolasThreeHalfZeroWeight.mul_left (2 * Real.sqrt (n : Real))).add
      (summable_robinXiZeroWeight.mul_left 5)).mul_right F
  calc
    _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
        norm (robinZeroKernel n (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p)) := norm_tsum_le_tsum_norm hSeries.norm
    _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
        (2 * Real.sqrt (n : Real) * nicolasThreeHalfZeroWeight p +
          5 * (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) * F) :=
      hSeries.norm.tsum_le_tsum (fun p => norm_nicolasDegreeZeroKernel_le hRH hn hx hL p)
        hMajor
    _ = _ := by
      rw [tsum_mul_right, Summable.tsum_add
        (summable_nicolasThreeHalfZeroWeight.mul_left (2 * Real.sqrt (n : Real)))
        (summable_robinXiZeroWeight.mul_left 5), tsum_mul_left, tsum_mul_left,
        robinXiZeroConstant_eq_of_riemannHypothesis hRH]
      rfl

def nicolasDegreeErrorConstant : Real :=
  2 * nicolasThreeHalfZeroConstant +
    5 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
      Real.log (2 * Real.pi)

theorem abs_nicolasDegreeError_le (hRH : RiemannHypothesis)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 2 <= x) (hL : 1 <= Real.log x) :
    abs (robinPsiWeightedErrorIntegral n x) <=
      nicolasDegreeErrorConstant * Real.sqrt (n : Real) *
        (x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x)) := by
  have hx1 : 1 < x := by linarith
  have hK := norm_tsum_nicolasDegreeZeroKernel_le hRH hn hx1 hL
  have hC := robinTrivialZeroCorrection_bounds (by omega : 1 <= n) hx
  have hFormula := robinPsiWeightedErrorIntegral_eq_zero_sum_correction hRH hn hx
  have hAbs : abs (robinPsiWeightedErrorIntegral n x) <=
      norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p)) + robinTrivialZeroCorrection n x := by
    have hTriangle := norm_sub_le
      (-tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p)) (robinTrivialZeroCorrection n x : Complex)
    rw [<- hFormula, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC.1] at hTriangle
    exact hTriangle
  have hS : 1 <= Real.sqrt (n : Real) := by
    rw [Real.le_sqrt (by norm_num : (0 : Real) <= 1) (Nat.cast_nonneg n)]
    norm_num
    exact_mod_cast (show 1 <= n by omega)
  have hBeta : 0 <= Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
    rw [<- robinXiZeroConstant_eq_of_riemannHypothesis hRH]
    exact tsum_nonneg (fun p => sq_nonneg _)
  have hLogPi : 0 <= Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hPower : x ^ (-(n : Real)) <= x ^ ((1 / 2 : Real) - n) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hCorrection := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hPower hLogPi)
    (inv_nonneg.mpr (Real.log_pos hx1).le)
  have hF : 0 <= x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x) := by positivity
  have hScale := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hS
      (show 0 <= 5 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
        Real.log (2 * Real.pi) by positivity)) hF
  dsimp [nicolasDegreeErrorConstant]
  nlinarith only [hAbs, hK, hC.2, hCorrection, hScale]

end PrimeFactorOscillations
