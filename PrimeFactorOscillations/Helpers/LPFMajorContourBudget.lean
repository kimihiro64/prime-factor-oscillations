/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Real.Pi.Bounds
import PrimeFactorOscillations.Helpers.LPFMajorZetaIntegral

/-!
# Complete numerical contour allowances

Height logs and contour locations match the character disk estimate.
Normalization of all three shifted edges gives coefficient 54912; the
Perron and principal-pole allowances then fit within 65536. These assembly
lemmas state their input inequalities explicitly. The actual character
prime-prefix application remains a separate theorem.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

theorem lpf_height_log_numeric (N x t : Real)
    (hN : 1 <= N) (hx : 3 <= x) (ht : abs t <= x) :
    1 + Real.log N + Real.log (abs t + 8) <=
      2 * (1 + Real.log N + Real.log (x + 2)) := by
  have hPos : 0 < abs t + 8 := by linarith [abs_nonneg t]
  have hPow : abs t + 8 <= (x + 2) ^ 2 := by nlinarith
  have hLog := Real.log_le_log hPos hPow
  rw [Real.log_pow] at hLog
  norm_num at hLog
  have hLogN := Real.log_nonneg hN
  linarith

theorem lpf_contour_point_distance (sigma t : Real)
    (hSigma : 15 / 16 <= sigma) (hTwo : sigma <= 2) :
    dist ((sigma : Complex) + Complex.I * (t : Complex))
      (2 + Complex.I * (t : Complex)) <= 17 / 16 := by
  have he : ((sigma : Complex) + Complex.I * (t : Complex)) -
      (2 + Complex.I * (t : Complex)) = (sigma : Complex) - 2 := by ring
  rw [dist_eq_norm, he]
  have hc : ((sigma - 2 : Real) : Complex) = (sigma : Complex) - 2 := by simp
  rw [<- hc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (show sigma - 2 <= 0 by linarith)]
  linarith

theorem lpf_normalized_vertical_norm (z : Complex) :
    norm ((1 / (2 * (Real.pi : Complex) * Complex.I)) * Complex.I * z) =
      (1 / (2 * Real.pi)) * norm z := by
  simp only [norm_mul, norm_div, norm_one, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    show norm (2 : Complex) = (2 : Real) by norm_num, mul_one]

theorem lpf_contour_numeric_budget (B R c : Real) (z : Complex)
    (hB : 1 <= B) (hR : 1 <= R) (hc : c <= 2)
    (hNorm : norm z <=
      2 * (79872 * B * R) * B + 2 * (c - 15 / 16) * (79872 * B)) :
    norm ((1 / (2 * (Real.pi : Complex) * Complex.I)) * Complex.I * z) <=
      54912 * R * B ^ 2 := by
  have hB0 : 0 <= B := by linarith
  have hCoeff : 0 <= 2 * (79872 * B) := by positivity
  have hSide : 2 * (c - 15 / 16) * (79872 * B) <= 169728 * B := by
    calc
      _ = (2 * (79872 * B)) * (c - 15 / 16) := by ring
      _ <= (2 * (79872 * B)) * (17 / 16) :=
        mul_le_mul_of_nonneg_left (by linarith) hCoeff
      _ = _ := by ring
  have hBsq : B <= B ^ 2 := by nlinarith
  have hRBsq : B ^ 2 <= R * B ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hR (sq_nonneg B)
  have hBR : B <= R * B ^ 2 := hBsq.trans hRBsq
  have hTotal : norm z <= 329472 * R * B ^ 2 := by
    nlinarith only [hNorm, hSide, hBR]
  have hPi : (6 : Real) <= 2 * Real.pi := by linarith [Real.pi_gt_three]
  rw [lpf_normalized_vertical_norm]
  have hEq : (1 / (2 * Real.pi)) * norm z = norm z / (2 * Real.pi) := by ring
  rw [hEq]
  calc
    norm z / (2 * Real.pi) <= norm z / 6 :=
      div_le_div_of_nonneg_left (norm_nonneg z) (by norm_num) hPi
    _ <= (329472 * R * B ^ 2) / 6 :=
      div_le_div_of_nonneg_right hTotal (by norm_num)
    _ = _ := by ring

theorem lpf_chebyshev_numeric_budget (B R A E P : Real)
    (hB : 1 <= B) (hR : 1 <= R)
    (hA : A <= 54912 * R * B ^ 2) (hE : E <= 88 * B ^ 2) (hP : P <= 3) :
    A + E + P <= 65536 * R * B ^ 2 := by
  have hB2 : 1 <= B ^ 2 := by nlinarith
  have hRB2 : B ^ 2 <= R * B ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hR (sq_nonneg B)
  nlinarith only [hA, hE, hP, hB2, hRB2]

end PrimeFactorOscillations.QRH

