/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasDegreeLocalization
import PrimeFactorOscillations.Helpers.NicolasPrimeSquareBias
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.SignedIteratedRemainder

/-!
# The spectral expansion of the finite Nicolas logarithm

The actual theta error controls the signed tangent remainder. Both signs
are retained before combining it with the exact finite-product identity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter Robin1984

def nicolasPointwiseThetaConstant : Real :=
  13 + 12 * (abs nicolasDegreeErrorConstant + 1)

def nicolasHeightTangentError (x : Real) : Real :=
  (Chebyshev.theta x - x) / (x * Real.log x) -
    (Real.log (Real.log (Chebyshev.theta x)) - Real.log (Real.log x))

theorem eventually_nicolasHeight_domain (hRH : RiemannHypothesis) :
    Filter.Eventually (fun x : Real =>
      max 4 (2 * Real.exp 1) <= x /\
      x <= 2 * Chebyshev.theta x /\
      1 <= Real.log (Chebyshev.theta x)) atTop := by
  let K := nicolasPointwiseThetaConstant
  have hK : 0 < K := by dsimp [K, nicolasPointwiseThetaConstant]; positivity
  filter_upwards [eventually_ge_atTop (max (max 4 (2 * Real.exp 1)) ((2 * K) ^ (3 : Nat)))]
    with x hx
  have hxBase : max 4 (2 * Real.exp 1) <= x := (le_max_left _ _).trans hx
  have hx4 : 4 <= x := (le_max_left _ _).trans hxBase
  have hxPos : 0 < x := by linarith
  have hxExp : 2 * Real.exp 1 <= x := (le_max_right _ _).trans hxBase
  have hLog : 1 <= Real.log (x / 2) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 <= x / 2 by linarith)
    simpa only [Real.log_exp] using h
  have hError : abs (Chebyshev.theta x - x) <= K * x ^ (2 / 3 : Real) :=
    abs_nicolasThetaError_le_two_thirds hRH hx4 hLog
  have hCube : ((2 * K) ^ (3 : Nat)) ^ (1 / 3 : Real) = 2 * K := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (show 0 <= 2 * K by positivity)]
    norm_num
  have hRoot := Real.rpow_le_rpow (show 0 <= (2 * K) ^ (3 : Nat) by positivity)
    ((le_max_right _ _).trans hx) (by norm_num : (0 : Real) <= 1 / 3)
  rw [hCube] at hRoot
  have hProduct : x ^ (1 / 3 : Real) * x ^ (2 / 3 : Real) = x := by
    rw [<- Real.rpow_add hxPos]
    norm_num
  have hScale := mul_le_mul_of_nonneg_right hRoot
    (Real.rpow_nonneg hxPos.le (2 / 3 : Real))
  have hHalf : K * x ^ (2 / 3 : Real) <= x / 2 := by
    nlinarith only [hScale, hProduct]
  have hThetaHalf : x / 2 <= Chebyshev.theta x := by
    linarith only [(abs_le.mp hError).1, hHalf]
  refine And.intro hxBase (And.intro (by linarith) ?_)
  have hThetaExp : Real.exp 1 <= Chebyshev.theta x := by linarith only [hThetaHalf, hxExp]
  have h := Real.log_le_log (Real.exp_pos 1) hThetaExp
  simpa only [Real.log_exp] using h

theorem eventually_abs_nicolasHeightTangentError_le (hRH : RiemannHypothesis) :
    Filter.Eventually (fun x : Real =>
      abs (nicolasHeightTangentError x) <=
        36 * nicolasPointwiseThetaConstant ^ 2 *
          x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2)) atTop := by
  have hPowerToSpectral
      {x E K : Real} (hx : 1 < x)
      (hE : abs E <= K * x ^ (2 / 3 : Real)) :
      6 * E ^ 2 / (x ^ 2 * Real.log x) <=
        36 * K ^ 2 * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
    have hxPos : 0 < x := by linarith
    have hLogPos : 0 < Real.log x := Real.log_pos hx
    have hSquare : E ^ 2 <= (K * x ^ (2 / 3 : Real)) ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg E) hE
      simpa only [<- pow_two, sq_abs] using h
    have hD := (div_le_div_iff_of_pos_right
      (show 0 < x ^ 2 * Real.log x by positivity)).2
        (mul_le_mul_of_nonneg_left hSquare (by norm_num : (0 : Real) <= 6))
    have hPowers : (x ^ (2 / 3 : Real)) ^ (2 : Nat) =
        x ^ (2 : Nat) * x ^ (-(2 / 3 : Real)) := by
      rw [<- Real.rpow_natCast, <- Real.rpow_mul hxPos.le,
        <- Real.rpow_natCast, <- Real.rpow_add hxPos]
      congr 1
      norm_num
    have hNormalize :
        6 * (K * x ^ (2 / 3 : Real)) ^ 2 / (x ^ 2 * Real.log x) =
          6 * K ^ 2 * x ^ (-(2 / 3 : Real)) * Inv.inv (Real.log x) := by
      rw [mul_pow, hPowers]
      field_simp
    have hLog : Real.log x <= 6 * x ^ (1 / 6 : Real) := by
      have h := Real.log_le_rpow_div hxPos.le (by norm_num : (0 : Real) < 1 / 6)
      convert h using 1
      ring
    have hPowerStep : x ^ (-(2 / 3 : Real)) * x ^ (1 / 6 : Real) =
        x ^ (-(1 / 2 : Real)) := by
      rw [<- Real.rpow_add hxPos]
      congr 1
      norm_num
    have hScale : x ^ (-(2 / 3 : Real)) * Inv.inv (Real.log x) <=
        6 * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hLog
        (show 0 <= x ^ (-(2 / 3 : Real)) * Inv.inv ((Real.log x) ^ 2) by positivity)
      calc
        _ = x ^ (-(2 / 3 : Real)) * Real.log x * Inv.inv ((Real.log x) ^ 2) := by
          field_simp
        _ <= 6 * (x ^ (-(2 / 3 : Real)) * x ^ (1 / 6 : Real)) *
            Inv.inv ((Real.log x) ^ 2) := by nlinarith only [h]
        _ = _ := by rw [hPowerStep]
    rw [hNormalize] at hD
    have hFinal := mul_le_mul_of_nonneg_left hScale
      (show 0 <= 6 * K ^ 2 by positivity)
    nlinarith only [hD, hFinal]
  filter_upwards [eventually_nicolasHeight_domain hRH] with x hx
  have hx4 : 4 <= x := (le_max_left _ _).trans hx.1
  have hx1 : 1 < x := by linarith
  have hxExp : 2 * Real.exp 1 <= x := (le_max_right _ _).trans hx.1
  have hLogHalf : 1 <= Real.log (x / 2) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 <= x / 2 by linarith)
    simpa only [Real.log_exp] using h
  have hLog : 1 <= Real.log x :=
    hLogHalf.trans (Real.log_le_log (by linarith : 0 < x / 2) (by linarith : x / 2 <= x))
  have hTaylor := Real.logLog_remainder_abs_le hx1
    (one_lt_chebyshevTheta_of_three_le (by linarith)) hLog hx.2.2 hx.2.1
  have hError := abs_nicolasThetaError_le_two_thirds hRH hx4 hLogHalf
  exact hTaylor.trans (hPowerToSpectral hx1 hError)


def nicolasLogSpectralConstant : Real :=
  abs (10 + 45 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
    4 * Real.log (2 * Real.pi) + (Real.log 4 + 4) * (79 / 3 : Real)) +
    36 * nicolasPointwiseThetaConstant ^ 2 + 64

theorem nicolasLogSpectralConstant_pos : 0 < nicolasLogSpectralConstant := by
  unfold nicolasLogSpectralConstant
  positivity

theorem eventually_nicolasLog_wave_uniform_error (hRH : RiemannHypothesis) :
    Filter.Eventually (fun x : Real =>
      abs (nicolasLogMertensOscillation x + (2 + nicolasZeroWave x) /
        (x ^ (1 / 2 : Real) * Real.log x)) <=
      nicolasLogSpectralConstant * x ^ (-(1 / 2 : Real)) *
        Inv.inv ((Real.log x) ^ 2)) atTop := by
  filter_upwards [eventually_nicolasHeight_domain hRH,
    eventually_abs_nicolasHeightTangentError_le hRH] with x hx hHeight
  have hx4 : 4 <= x := (le_max_left _ _).trans hx.1
  have hx1 : 1 < x := by linarith
  have hxPos : 0 < x := by linarith
  have hxExp : 2 * Real.exp 1 <= x := (le_max_right _ _).trans hx.1
  have hLog : 1 <= Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 <= x by linarith [Real.exp_pos 1])
    simpa only [Real.log_exp] using h
  have hLogPos : 0 < Real.log x := Real.log_pos hx1
  have hFour : 4 / x <= 64 * x ^ (-(1 / 2 : Real)) *
      Inv.inv ((Real.log x) ^ 2) := by
    have hlog : Real.log x <= 4 * x ^ (1 / 4 : Real) := by
      have h := Real.log_le_rpow_div hxPos.le (by norm_num : (0 : Real) < 1 / 4)
      convert h using 1
      ring
    have hQuarter : (x ^ (1 / 4 : Real)) ^ (2 : Nat) = x ^ (1 / 2 : Real) := by
      rw [<- Real.rpow_natCast, <- Real.rpow_mul hxPos.le]
      congr 1
      norm_num
    have hRootSq : (x ^ (1 / 2 : Real)) ^ (2 : Nat) = x := by
      rw [<- Real.rpow_natCast, <- Real.rpow_mul hxPos.le]
      norm_num
    have hSquare : (Real.log x) ^ 2 <= 16 * x ^ (1 / 2 : Real) := by
      have h := mul_self_le_mul_self hLogPos.le hlog
      simpa only [<- pow_two, mul_pow, hQuarter, show (4 : Real) ^ 2 = 16 by norm_num] using h
    have hInv := one_div_le_one_div_of_le (sq_pos_of_pos hLogPos) hSquare
    have h := mul_le_mul_of_nonneg_left hInv
      (show 0 <= 64 * x ^ (-(1 / 2 : Real)) by positivity)
    have hId : 64 * x ^ (-(1 / 2 : Real)) * (1 / (16 * x ^ (1 / 2 : Real))) =
        4 / x := by
      rw [Real.rpow_neg hxPos.le]
      have hRootPos := Real.rpow_pos_of_pos hxPos (1 / 2 : Real)
      field_simp
      nlinarith only [hRootSq]
    rw [hId] at h
    simpa only [one_div] using h
  let A := Finset.sum (Finset.Ioc 0 (Nat.floor x)) (fun n => Mertens.M_eq_summand n) -
    (Mertens.M - Real.eulerMascheroniConstant)
  let K0 := 10 + 45 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
    4 * Real.log (2 * Real.pi) + (Real.log 4 + 4) * (79 / 3 : Real)
  have hA : abs A <= 4 / x := nicolasMertensSummandTail_le (by linarith)
  have hK := nicolasK_wave_uniform_error hRH hx4 hLog
  have hCoeff : K0 * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) <=
      abs K0 * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self K0) (Real.rpow_nonneg hxPos.le _))
      (inv_nonneg.mpr (sq_nonneg _))
  have hKFinal := hK.trans hCoeff
  have hSplit : nicolasLogMertensOscillation x + (2 + nicolasZeroWave x) /
        (x ^ (1 / 2 : Real) * Real.log x) =
      (A - nicolasHeightTangentError x) +
        (nicolasK x + (2 + nicolasZeroWave x) / (x ^ (1 / 2 : Real) * Real.log x)) := by
    rw [nicolasLogMertensOscillation_eq_components (by linarith)]
    dsimp [A, nicolasHeightTangentError, nicolasThetaError]
    ring
  have hSub : abs (A - nicolasHeightTangentError x) <=
      abs A + abs (nicolasHeightTangentError x) := by
    simpa only [Real.norm_eq_abs] using norm_sub_le A (nicolasHeightTangentError x)
  have hTriangle := abs_add_le (A - nicolasHeightTangentError x)
    (nicolasK x + (2 + nicolasZeroWave x) / (x ^ (1 / 2 : Real) * Real.log x))
  rw [hSplit]
  dsimp [nicolasLogSpectralConstant]
  dsimp [K0] at hKFinal
  nlinarith only [hTriangle, hSub, hA.trans hFour, hHeight, hKFinal]

end PrimeFactorOscillations
