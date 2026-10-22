/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianLeftIntegration
import PrimeFactorOscillations.Helpers.LogGaussianZeroPairing

/-!
# A summable uniform bound for the omitted part of every zero term

The full signed integration-by-parts identity gives two factors 1/rho.
Only this separated left-tail error is estimated in modulus.
The principal Gaussian moment remains unchanged.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set Filter

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianLeftZeroError
    (X V tau : Real) (rho : Complex) : Complex :=
  (X : Complex) ^ rho / rho *
    integral (volume.restrict (Iic (-Real.log X))) (logGaussianWeightedWave V tau rho)

theorem logGaussian_left_derivative_integral_norm_bound
    (V tau a : Real) (rho : Complex) (hV : 1 <= V) (hRe : -1 < rho.re) :
    norm (integral (volume.restrict (Iic a)) (fun u : Real =>
      Complex.exp (rho * (u : Complex)) *
        (logGaussianWaveSlope V tau u * logGaussianWave V tau u))) <=
      (4 + abs tau) * logGaussianTailScale V * Real.exp ((rho.re + 1) * a) / (rho.re + 1) := by
  have hc : 0 < rho.re + 1 := by linarith only [hRe]
  have hG := logGaussian_left_derivative_term_integrable V tau a rho hV hRe
  have hM := (integrableOn_exp_mul_Iic hc a).const_mul
    ((4 + abs tau) * logGaussianTailScale V)
  calc
    _ <= integral (volume.restrict (Iic a)) (fun u : Real =>
        norm (Complex.exp (rho * (u : Complex)) *
          (logGaussianWaveSlope V tau u * logGaussianWave V tau u))) :=
      norm_integral_le_integral_norm _
    _ <= integral (volume.restrict (Iic a)) (fun u : Real =>
        ((4 + abs tau) * logGaussianTailScale V) * Real.exp ((rho.re + 1) * u)) := by
      apply integral_mono_ae hG.norm hM
      exact Eventually.of_forall fun u =>
        logGaussian_left_derivative_term_norm_bound V tau u rho hV
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Iic hc a]
      ring

theorem logGaussianLeftZeroError_eq_boundary_sub_derivative
    (X V tau : Real) (rho : Complex) (hX : 0 < X) (hV : 1 <= V)
    (hRho : Not (rho = 0)) (hRe : -1 < rho.re) :
    logGaussianLeftZeroError X V tau rho =
      (logGaussianWave V tau (-Real.log X) -
        (X : Complex) ^ rho * integral (volume.restrict (Iic (-Real.log X))) (fun u : Real =>
          Complex.exp (rho * (u : Complex)) *
            (logGaussianWaveSlope V tau u * logGaussianWave V tau u))) / rho ^ 2 := by
  have hXc : Not ((X : Complex) = 0) := Complex.ofReal_ne_zero.mpr hX.ne'
  have he : Complex.log (X : Complex) * rho + rho * ((-Real.log X : Real) : Complex) = 0 := by
    rw [<- Complex.ofReal_log hX.le]
    push_cast
    ring
  have hCancel : (X : Complex) ^ rho *
      Complex.exp (rho * ((-Real.log X : Real) : Complex)) = 1 := by
    rw [Complex.cpow_def_of_ne_zero hXc, <- Complex.exp_add, he, Complex.exp_zero]
  have hBoundary : (X : Complex) ^ rho *
      logGaussianWeightedWave V tau rho (-Real.log X) = logGaussianWave V tau (-Real.log X) := by
    rw [logGaussianWeightedWave, <- mul_assoc, hCancel, one_mul]
  have hI := logGaussian_left_integration_by_parts V tau (-Real.log X) rho hV hRe
  have hSub := (eq_sub_iff_add_eq).mpr hI
  apply (eq_div_iff (pow_ne_zero 2 hRho)).mpr
  calc
    logGaussianLeftZeroError X V tau rho * rho ^ 2 =
        (X : Complex) ^ rho *
          (rho * integral (volume.restrict (Iic (-Real.log X))) (logGaussianWeightedWave V tau rho)) := by
      dsimp [logGaussianLeftZeroError]
      field_simp [hRho]
    _ = _ := by
      rw [hSub, mul_sub, hBoundary]

theorem logGaussianLeftZeroError_norm_bound
    (X V tau : Real) (rho : Complex) (hX : 0 < X) (hV : 1 <= V)
    (hRho : Not (rho = 0)) (hRe : 0 <= rho.re) :
    norm (logGaussianLeftZeroError X V tau rho) <=
      ((5 + abs tau) * logGaussianTailScale V / X) *
        (Inv.inv (norm rho)) ^ (2 : Nat) := by
  have hVPos : 0 < V := lt_of_lt_of_le Real.zero_lt_one hV
  have hRe' : -1 < rho.re := by linarith only [hRe]
  let B : Real := logGaussianTailScale V
  let K : Real := (4 + abs tau) * B
  let a : Real := -Real.log X
  let c : Real := rho.re + 1
  let J : Complex := integral (volume.restrict (Iic a)) (fun u : Real =>
    Complex.exp (rho * (u : Complex)) *
      (logGaussianWaveSlope V tau u * logGaussianWave V tau u))
  have hB : 0 <= B := (logGaussianTailScale_pos V hVPos).le
  have hK : 0 <= K := mul_nonneg (by positivity) hB
  have hc : 1 <= c := by dsimp [c]; linarith only [hRe]
  have hExp : Real.exp (-Real.log X) = 1 / X := by
    rw [Real.exp_neg, Real.exp_log hX, one_div]
  have hPower : X ^ rho.re * Real.exp (c * a) = 1 / X := by
    rw [Real.rpow_def_of_pos hX, <- Real.exp_add]
    have he : Real.log X * rho.re + c * a = -Real.log X := by dsimp [c, a]; ring
    rw [he, hExp]
  have hWave : norm (logGaussianWave V tau a) <= B / X := by
    rw [logGaussianWave_norm V tau a hVPos]
    have h := logGaussianDensity_le_left_exponential V a hVPos
    simpa only [a, hExp, B, mul_one_div] using h
  have hJ : norm J <= K * Real.exp (c * a) / c :=
    logGaussian_left_derivative_integral_norm_bound V tau a rho hV hRe'
  have hPair : norm ((X : Complex) ^ rho * J) <= K / X := by
    calc
      _ = X ^ rho.re * norm J := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
      _ <= X ^ rho.re * (K * Real.exp (c * a) / c) :=
        mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hX.le _)
      _ = K / (X * c) := by
        rw [show X ^ rho.re * (K * Real.exp (c * a) / c) =
          K * (X ^ rho.re * Real.exp (c * a)) / c by ring, hPower]
        ring
      _ <= K / X := by
        apply div_le_div_of_nonneg_left hK hX
        have h := mul_le_mul_of_nonneg_left hc hX.le
        simpa only [mul_one] using h
  have hNumerator :
      norm (logGaussianWave V tau a - (X : Complex) ^ rho * J) <=
        (5 + abs tau) * B / X := by
    calc
      _ <= norm (logGaussianWave V tau a) + norm ((X : Complex) ^ rho * J) := norm_sub_le _ _
      _ <= B / X + K / X := add_le_add hWave hPair
      _ = _ := by dsimp [K]; ring
  rw [logGaussianLeftZeroError_eq_boundary_sub_derivative X V tau rho hX hV hRho hRe',
    norm_div, norm_pow]
  change norm (logGaussianWave V tau a - (X : Complex) ^ rho * J) / norm rho ^ 2 <= _
  calc
    _ <= ((5 + abs tau) * B / X) / norm rho ^ 2 :=
      div_le_div_of_nonneg_right hNumerator (sq_nonneg (norm rho))
    _ = _ := by rw [div_eq_mul_inv, inv_pow]

theorem logGaussianLeftZeroError_xi_summable
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      logGaussianLeftZeroError X V tau (riemannXiDivisorZeroValue p)) := by
  apply Summable.of_norm_bounded
    (summable_riemannXiDivisorZero_norm_inv_sq.mul_left
      ((5 + abs tau) * logGaussianTailScale V / X))
  intro p
  exact logGaussianLeftZeroError_norm_bound X V tau (riemannXiDivisorZeroValue p) hX hV
    (riemannXiDivisorZeroValue_ne_zero p) (xiDivisorZeroValue_re_bounds p).1.le

theorem logGaussianLeftZeroError_xi_sum_norm_bound
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
      logGaussianLeftZeroError X V tau (riemannXiDivisorZeroValue p))) <=
      ((5 + abs tau) * logGaussianTailScale V / X) *
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) := by
  have hError := logGaussianLeftZeroError_xi_summable X V tau hX hV
  have hMajor := summable_riemannXiDivisorZero_norm_inv_sq.mul_left
    ((5 + abs tau) * logGaussianTailScale V / X)
  calc
    _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
        norm (logGaussianLeftZeroError X V tau (riemannXiDivisorZeroValue p))) :=
      norm_tsum_le_tsum_norm hError.norm
    _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
        ((5 + abs tau) * logGaussianTailScale V / X) *
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) := by
      apply Summable.tsum_le_tsum _ hError.norm hMajor
      intro p
      exact logGaussianLeftZeroError_norm_bound X V tau (riemannXiDivisorZeroValue p)
        hX hV (riemannXiDivisorZeroValue_ne_zero p) (xiDivisorZeroValue_re_bounds p).1.le
    _ = _ := tsum_mul_left

end PrimeFactorOscillations.PrimeClassDeletion
