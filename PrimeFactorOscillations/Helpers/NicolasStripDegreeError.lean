/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasStripPowerMoment
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedStripEndpoint

/-!
# The complete weighted psi error with an arbitrary fractional degree loss

All canonical zeros, inverse-square remainders, and the entire scalar
correction are retained. The upper strip and delta remain explicit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Robin1984

private theorem strip_degree_remainder_scalar
    {n : Nat} (hn : 2 <= n) {b : Real} (hb : b <= 1)
    {x : Real} (hx : 1 < x) (hL : 1 <= Real.log x) :
    x ^ (b - (n : Real)) * Inv.inv ((Real.log x) ^ (2 : Nat)) +
      2 * ((-x ^ (b - (n : Real)) / (b - (n : Real))) *
        Inv.inv ((Real.log x) ^ (3 : Nat))) <=
      3 * (x ^ (b - (n : Real)) * Inv.inv (Real.log x)) := by
  let E : Real := x ^ (b - (n : Real))
  let v : Real := Inv.inv (Real.log x)
  have hE : 0 <= E := Real.rpow_nonneg (by linarith only [hx]) _
  have hv : 0 <= v := inv_nonneg.mpr (by linarith only [hL])
  have hvOne : v <= 1 := by
    simpa only [one_div, inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hL
  have hvTwo : v ^ (2 : Nat) <= v := by
    nlinarith only [mul_nonneg hv (sub_nonneg.mpr hvOne)]
  have hvThree : v ^ (3 : Nat) <= v := by
    have h := mul_le_mul_of_nonneg_left hvTwo hv
    nlinarith only [h, hvTwo]
  have hnR : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hDen : 1 <= (n : Real) - b := by linarith only [hnR, hb]
  have hDenPos : 0 < (n : Real) - b := by linarith only [hDen]
  have hNeg : b - (n : Real) < 0 := by linarith only [hDen]
  have hInv := one_div_le_one_div_of_le
    (by norm_num : (0 : Real) < 1) hDen
  have hInvScaled := mul_le_mul_of_nonneg_left hInv hE
  have hTail : -E / (b - (n : Real)) <= E := by
    have hEq : -E / (b - (n : Real)) = E * (1 / ((n : Real) - b)) := by
      field_simp [hDenPos.ne', hNeg.ne]
      ring
    rw [hEq]
    simpa only [one_div_one, mul_one] using hInvScaled
  have hA := mul_le_mul_of_nonneg_left hvTwo hE
  have hB := mul_le_mul_of_nonneg_right hTail (pow_nonneg hv 3)
  have hC := mul_le_mul_of_nonneg_left hvThree hE
  have hResult : E * v ^ (2 : Nat) +
      2 * ((-E / (b - (n : Real))) * v ^ (3 : Nat)) <= 3 * (E * v) := by
    nlinarith only [hA, hB, hC]
  simpa only [E, v, inv_pow] using hResult

theorem norm_nicolasStripDegreeZeroKernel_le
    {eta : Real} {rho : Complex} (hRho : Not (rho = 0))
    (hRe : rho.re <= eta) (hEta : eta <= 1)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x)
    (hL : 1 <= Real.log x) :
    norm (robinZeroKernel n rho x / rho) <=
      (norm (((n : Complex) / ((n : Complex) - rho)) / rho) +
        3 * (Inv.inv (norm rho)) ^ (2 : Nat)) *
          (x ^ (eta - (n : Real)) * Inv.inv (Real.log x)) := by
  have hReOne : rho.re <= 1 := hRe.trans hEta
  have hnR : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hReN : rho.re < (n : Real) := by linarith only [hReOne, hnR]
  have hLog : 0 < Real.log x := Real.log_pos hx
  have hNorm :
      norm ((x : Complex) ^ (rho - (n : Complex)) *
        ((Inv.inv (Real.log x) : Real) : Complex)) =
          x ^ (rho.re - (n : Real)) * Inv.inv (Real.log x) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith only [hx]),
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hLog)]
    simp only [Complex.sub_re, Complex.natCast_re]
  have hRewrite :
      ((n : Complex) / ((n : Complex) - rho) *
        (x : Complex) ^ (rho - (n : Complex)) *
          ((Inv.inv (Real.log x) : Real) : Complex)) / rho =
      (((n : Complex) / ((n : Complex) - rho)) / rho) *
        ((x : Complex) ^ (rho - (n : Complex)) *
          ((Inv.inv (Real.log x) : Real) : Complex)) := by ring
  have hRem := norm_robinZeroKernelRemainder_div_rho_le_re hn hRho hReOne hx
  have hScalar := mul_le_mul_of_nonneg_left
    (strip_degree_remainder_scalar hn hReOne hx hL)
    (sq_nonneg (Inv.inv (norm rho)))
  have hTriangle := norm_add_le
    ((((n : Complex) / ((n : Complex) - rho)) / rho) *
      ((x : Complex) ^ (rho - (n : Complex)) *
        ((Inv.inv (Real.log x) : Real) : Complex)))
    (robinZeroKernelRemainder n rho x / rho)
  rw [norm_mul, hNorm] at hTriangle
  rw [robinZeroKernel_eq_main_add_remainder (by omega : 1 <= n) hx hReN,
    add_div, hRewrite]
  have hRaw :
      norm ((((n : Complex) / ((n : Complex) - rho)) / rho) *
          ((x : Complex) ^ (rho - (n : Complex)) *
            ((Inv.inv (Real.log x) : Real) : Complex)) +
        robinZeroKernelRemainder n rho x / rho) <=
      (norm (((n : Complex) / ((n : Complex) - rho)) / rho) +
        3 * (Inv.inv (norm rho)) ^ (2 : Nat)) *
          (x ^ (rho.re - (n : Real)) * Inv.inv (Real.log x)) := by
    nlinarith only [hTriangle, hRem, hScalar]
  have hPower := Real.rpow_le_rpow_of_exponent_le
    (by linarith only [hx] : 1 <= x) (sub_le_sub_right hRe (n : Real))
  exact hRaw.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hPower (inv_nonneg.mpr hLog.le))
    (by positivity))

theorem exists_nicolasStripDegreeError_bound
    (eta delta : Real) (hEtaZero : 0 <= eta) (hEtaOne : eta < 1)
    (hd : 0 < delta) (hdOne : delta <= 1)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= eta) :
    Exists fun D : Real => And (0 < D) (forall n : Nat, 2 <= n ->
      forall x : Real, 2 <= x -> 1 <= Real.log x ->
        abs (robinPsiWeightedErrorIntegral n x) <=
          D * (n : Real) ^ delta *
            (x ^ (eta - (n : Real)) * Inv.inv (Real.log x))) := by
  have hUpperOne (p : RiemannXiDivisorZeroIndex) :
      (riemannXiDivisorZeroValue p).re <= 1 := (hUpper p).trans hEtaOne.le
  choose C hC hCoefficient using exists_nicolasZeroCoefficient_power_bound
    delta hd hdOne hUpperOne
  let W : RiemannXiDivisorZeroIndex -> Real := fun p =>
    (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)
  have hW : Summable W := summable_robinXiZeroWeight
  have hS : 0 <= tsum W := tsum_nonneg (fun p => sq_nonneg _)
  have hLogPi : 0 <= Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith only [Real.pi_gt_three])
  let B : Real := 3 * tsum W + Real.log (2 * Real.pi)
  let D : Real := C + B + 1
  have hB : 0 <= B := by dsimp only [B]; linarith only [hS, hLogPi]
  have hD : 0 < D := by dsimp only [D]; linarith only [hC, hB]
  apply Exists.intro D
  apply And.intro hD
  intro n hn x hx hL
  have hxOne : 1 < x := by linarith only [hx]
  have hLog : 0 < Real.log x := Real.log_pos hxOne
  let F : Real := x ^ (eta - (n : Real)) * Inv.inv (Real.log x)
  have hF : 0 <= F := by dsimp only [F]; positivity
  have hCoeffSum : Summable (fun p : RiemannXiDivisorZeroIndex =>
      norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
        riemannXiDivisorZeroValue p)) := by
    apply (hW.mul_left (n : Real)).of_nonneg_of_le (fun p => norm_nonneg _)
    intro p
    exact norm_nat_div_sub_div_le_strip_weight hn
      (riemannXiDivisorZeroValue_ne_zero p) (hUpperOne p)
  have hSeries := summable_robinZeroKernel_div_rho_strip hEtaOne hUpper hn hxOne
  have hMajor := (hCoeffSum.add (hW.mul_left 3)).mul_right F
  have hSum : norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
      robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p)) <=
      (C * (n : Real) ^ delta + 3 * tsum W) * F := by
    calc
      _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
          norm (robinZeroKernel n (riemannXiDivisorZeroValue p) x /
            riemannXiDivisorZeroValue p)) := norm_tsum_le_tsum_norm hSeries.norm
      _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
          (norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
            riemannXiDivisorZeroValue p) + 3 * W p) * F) :=
        hSeries.norm.tsum_le_tsum (fun p =>
          norm_nicolasStripDegreeZeroKernel_le (riemannXiDivisorZeroValue_ne_zero p)
            (hUpper p) hEtaOne.le hn hxOne hL) hMajor
      _ = (tsum (fun p : RiemannXiDivisorZeroIndex =>
          norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
            riemannXiDivisorZeroValue p)) + 3 * tsum W) * F := by
        rw [tsum_mul_right, Summable.tsum_add hCoeffSum (hW.mul_left 3), tsum_mul_left]
      _ <= _ := mul_le_mul_of_nonneg_right
        (by linarith only [hCoefficient n hn]) hF
  have hTrivial := robinTrivialZeroCorrection_bounds (by omega : 1 <= n) hx
  have hFormula := robinPsiWeightedErrorIntegral_eq_zero_sum_correction_strip hUpperOne hn hx
  have hAbs : abs (robinPsiWeightedErrorIntegral n x) <=
      norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p)) +
        robinTrivialZeroCorrection n x := by
    have hTriangle := norm_sub_le
      (-tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p))
      (robinTrivialZeroCorrection n x : Complex)
    rw [<- hFormula, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hTrivial.1] at hTriangle
    exact hTriangle
  have hPower : x ^ (-(n : Real)) <= x ^ (eta - (n : Real)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hx]) (by linarith only [hEtaZero])
  have hCorrection := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hPower hLogPi) (inv_nonneg.mpr hLog.le)
  have hBefore : abs (robinPsiWeightedErrorIntegral n x) <=
      (C * (n : Real) ^ delta + B) * F := by
    dsimp only [B, F] at *
    nlinarith only [hAbs, hSum, hTrivial.2, hCorrection]
  have hN : 1 <= (n : Real) ^ delta :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 <= n)) hd.le
  have hAllowance : C * (n : Real) ^ delta + B <= D * (n : Real) ^ delta := by
    dsimp only [D]
    nlinarith only [hN, mul_nonneg hB (sub_nonneg.mpr hN)]
  exact hBefore.trans (mul_le_mul_of_nonneg_right hAllowance hF)

end PrimeFactorOscillations
