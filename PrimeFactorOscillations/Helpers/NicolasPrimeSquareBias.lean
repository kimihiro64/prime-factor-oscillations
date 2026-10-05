/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPrimeSquareTail

/-!
# The leading prime-square bias

The square-root psi integral is retained exactly, then compared with the
half-power kernel. Its leading coefficient is two.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Robin1984

theorem nicolasHalfKernel_explicit_error {x : Real} (hx : 1 < x) :
    abs ((robinZeroKernel 1 (1 / 2 : Complex) x).re -
      2 * x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) <=
      2 * nicolasSpectralRemainderScale x := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hR := norm_robinZeroKernelRemainder_div_rho_le (n := 1) (rho := (1 / 2 : Complex))
    (by norm_num) (by norm_num) (by norm_num) hx
  norm_num [norm_div] at hR
  have hbound : norm (robinZeroKernelRemainder 1 (1 / 2 : Complex) x) <=
      2 * nicolasSpectralRemainderScale x := by
    dsimp [nicolasSpectralRemainderScale]
    nlinarith only [hR]
  have hraw := robinZeroKernel_eq_main_add_remainder (n := 1) (rho := (1 / 2 : Complex))
    (by norm_num) hx (by norm_num)
  norm_num at hraw
  have hpow : (x : Complex) ^ (-(1 / 2 : Complex)) =
      ((x ^ (-(1 / 2 : Real)) : Real) : Complex) := by
    have h := (Complex.ofReal_cpow hxpos.le (-(1 / 2 : Real))).symm
    norm_num only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] at h
    exact h
  rw [hpow, <- Complex.ofReal_inv] at hraw
  have hreal := congrArg Complex.re hraw
  norm_num [Complex.mul_re] at hreal
  have heq : (robinZeroKernel 1 (1 / 2 : Complex) x).re -
      2 * x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) =
        (robinZeroKernelRemainder 1 (1 / 2 : Complex) x).re := by
    rw [hreal]
    ring
  rw [heq]
  exact (Complex.abs_re_le_norm _).trans hbound

theorem nicolasPsiSquareTail_explicit_error (hRH : RiemannHypothesis)
    {x : Real} (hx : 4 <= x) :
    abs (nicolasPsiRootTail 2 x - (robinZeroKernel 1 (1 / 2 : Complex) x).re) <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        x ^ (-(3 / 4 : Real)) *
          (2 / Real.log x + 2 / (Real.log x) ^ 2 + 16 / (3 * (Real.log x) ^ 3)) +
      Real.log (2 * Real.pi) / (x * Real.log x) := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := zero_lt_one.trans hx1
  have hLog : Not (Real.log x = 0) := (Real.log_pos hx1).ne'
  have hRootTwo : 2 <= x ^ (1 / 2 : Real) := by
    have hSqrt := Real.sqrt_le_sqrt hx
    have hFour : Real.sqrt (4 : Real) = 2 := by
      convert Real.sqrt_sq (by norm_num : 0 <= (2 : Real)) using 1
      norm_num
    rw [hFour] at hSqrt
    simpa only [Real.sqrt_eq_rpow] using hSqrt
  have hRootOne : 1 < x ^ (1 / 2 : Real) := by linarith
  have hRootLog : 0 < Real.log (x ^ (1 / 2 : Real)) := Real.log_pos hRootOne
  have hsplit := integral_psi_root_mul_robinRealWeight_eq (n := 1) (k := 2)
    (by norm_num) (by norm_num) hx1
  have heq : nicolasPsiRootTail 2 x = (robinZeroKernel 1 (1 / 2 : Complex) x).re +
      (1 / 2 : Real) * robinPsiWeightedErrorIntegral 2 (x ^ (1 / 2 : Real)) := by
    simpa only [nicolasPsiRootTail, Nat.cast_ofNat, inv_eq_one_div,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Nat.mul_one] using hsplit
  have hTwo := robinPsiWeightedErrorIntegral_bounds_all hRH (n := 2) (by norm_num) hRootTwo
  norm_num only [Nat.cast_ofNat] at hTwo
  have hCorrPos : 0 <= Real.log (2 * Real.pi) *
      (x ^ (1 / 2 : Real)) ^ (-(2 : Real)) *
        Inv.inv (Real.log (x ^ (1 / 2 : Real))) := by
    have hK : 0 <= Real.log (2 * Real.pi) :=
      Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    positivity
  have hAbs : abs (robinPsiWeightedErrorIntegral 2 (x ^ (1 / 2 : Real))) <=
      robinPsiWeightedErrorScalar 2 (x ^ (1 / 2 : Real)) +
        Real.log (2 * Real.pi) * (x ^ (1 / 2 : Real)) ^ (-(2 : Real)) *
          Inv.inv (Real.log (x ^ (1 / 2 : Real))) := by
    apply abs_le.mpr
    exact And.intro (by linarith [hTwo.1]) (by linarith [hTwo.2])
  have hPowThree : (x ^ (1 / 2 : Real)) ^ (-(3 / 2 : Real)) =
      x ^ (-(3 / 4 : Real)) := by
    rw [<- Real.rpow_mul hxpos.le]
    norm_num
  have hPowTwo : (x ^ (1 / 2 : Real)) ^ (-(2 : Real)) = x ^ (-(1 : Real)) := by
    rw [<- Real.rpow_mul hxpos.le]
    norm_num
  have hLogRoot : Real.log (x ^ (1 / 2 : Real)) = Real.log x / 2 := by
    rw [Real.log_rpow hxpos]
    ring
  have hScalar : (1 / 2 : Real) * robinPsiWeightedErrorScalar 2 (x ^ (1 / 2 : Real)) =
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        x ^ (-(3 / 4 : Real)) *
          (2 / Real.log x + 2 / (Real.log x) ^ 2 + 16 / (3 * (Real.log x) ^ 3)) := by
    dsimp [robinPsiWeightedErrorScalar]
    norm_num
    rw [hPowThree, hLogRoot]
    field_simp [hLog]
    ring
  have hCorrection : (1 / 2 : Real) *
      (Real.log (2 * Real.pi) * (x ^ (1 / 2 : Real)) ^ (-(2 : Real)) *
        Inv.inv (Real.log (x ^ (1 / 2 : Real)))) =
      Real.log (2 * Real.pi) / (x * Real.log x) := by
    rw [hPowTwo, Real.rpow_neg_one, hLogRoot]
    field_simp [hxpos.ne', hLog]
  calc
    _ = (1 / 2 : Real) * abs (robinPsiWeightedErrorIntegral 2 (x ^ (1 / 2 : Real))) := by
      rw [heq, add_sub_cancel_left, abs_mul]
      norm_num
    _ <= (1 / 2 : Real) *
        (robinPsiWeightedErrorScalar 2 (x ^ (1 / 2 : Real)) +
          Real.log (2 * Real.pi) * (x ^ (1 / 2 : Real)) ^ (-(2 : Real)) *
            Inv.inv (Real.log (x ^ (1 / 2 : Real)))) :=
      mul_le_mul_of_nonneg_left hAbs (by norm_num)
    _ = _ := by rw [mul_add, hScalar, hCorrection]


theorem nicolasPsiSquareTail_uniform_error (hRH : RiemannHypothesis)
    {x : Real} (hx : 4 <= x) (hlog : 1 <= Real.log x) :
    abs (nicolasPsiRootTail 2 x - (robinZeroKernel 1 (1 / 2 : Complex) x).re) <=
      (40 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
        2 * Real.log (2 * Real.pi)) *
          x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := zero_lt_one.trans hx1
  have hlpos : 0 < Real.log x := Real.log_pos hx1
  let beta := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  let B := x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2)
  have hb : 0 <= beta := (abs_nonneg _).trans (abs_nicolasZeroWave_le hRH hx1)
  have hK : 0 <= Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hi2 : (1 : Real) / (Real.log x) ^ 2 <= 1 / Real.log x :=
    one_div_le_one_div_of_le hlpos (by nlinarith only [hlog])
  have hi3 : (1 : Real) / (Real.log x) ^ 3 <= 1 / Real.log x :=
    one_div_le_one_div_of_le hlpos (by
      have h := mul_le_mul_of_nonneg_right hlog (sq_nonneg (Real.log x))
      nlinarith only [hlog, h])
  have hbracket : 2 / Real.log x + 2 / (Real.log x) ^ 2 +
      16 / (3 * (Real.log x) ^ 3) <= 10 * Inv.inv (Real.log x) := by
    have hi : 0 <= (1 : Real) / Real.log x := by positivity
    calc
      _ = 2 * (1 / Real.log x) + 2 * (1 / (Real.log x) ^ 2) +
          (16 / 3 : Real) * (1 / (Real.log x) ^ 3) := by ring
      _ <= 10 * (1 / Real.log x) := by linarith only [hi2, hi3, hi]
      _ = _ := by rw [one_div]
  have hlogq : Real.log x <= 4 * x ^ (1 / 4 : Real) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos (1 / 4 : Real))
    rw [Real.log_rpow hxpos] at h
    linarith only [h]
  have hpowq : x ^ (1 / 4 : Real) * x ^ (-(3 / 4 : Real)) =
      x ^ (-(1 / 2 : Real)) := by
    rw [<- Real.rpow_add hxpos]
    norm_num
  have hquarter : x ^ (-(3 / 4 : Real)) * Inv.inv (Real.log x) <= 4 * B := by
    calc
      _ = Real.log x * (x ^ (-(3 / 4 : Real)) * Inv.inv ((Real.log x) ^ 2)) := by
        field_simp
      _ <= (4 * x ^ (1 / 4 : Real)) *
          (x ^ (-(3 / 4 : Real)) * Inv.inv ((Real.log x) ^ 2)) :=
        mul_le_mul_of_nonneg_right hlogq (by positivity)
      _ = 4 * (x ^ (1 / 4 : Real) * x ^ (-(3 / 4 : Real))) *
          Inv.inv ((Real.log x) ^ 2) := by ring
      _ = _ := by rw [hpowq]; dsimp [B]; ring
  have hmain := mul_le_mul_of_nonneg_left hbracket
    (mul_nonneg hb (Real.rpow_nonneg hxpos.le (-(3 / 4 : Real))))
  have hquarterScaled := mul_le_mul_of_nonneg_left hquarter
    (show 0 <= 10 * beta by positivity)
  have hroot := Real.rpow_pos_of_pos hxpos (1 / 2 : Real)
  have hlogroot : Real.log x <= 2 * x ^ (1 / 2 : Real) := by
    have h := Real.log_le_sub_one_of_pos hroot
    rw [Real.log_rpow hxpos] at h
    linarith only [h]
  have hdiv : x ^ (-(1 / 2 : Real)) = x ^ (1 / 2 : Real) / x := by
    rw [show -(1 / 2 : Real) = 1 / 2 - 1 by norm_num, Real.rpow_sub hxpos, Real.rpow_one]
  have hcorrection : x ^ (-(1 : Real)) * Inv.inv (Real.log x) <= 2 * B := by
    have h := mul_le_mul_of_nonneg_right hlogroot
      (show 0 <= Inv.inv x * Inv.inv ((Real.log x) ^ 2) by positivity)
    dsimp [B]
    convert h using 1
    . rw [Real.rpow_neg hxpos.le, Real.rpow_one]
      field_simp
    . rw [hdiv]
      simp only [div_eq_mul_inv]
      ring
  have hcorrectionScaled := mul_le_mul_of_nonneg_left hcorrection hK
  have hcorrectionEq : Real.log (2 * Real.pi) / (x * Real.log x) =
      Real.log (2 * Real.pi) * (x ^ (-(1 : Real)) * Inv.inv (Real.log x)) := by
    rw [Real.rpow_neg_one]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have h := nicolasPsiSquareTail_explicit_error hRH hx
  rw [hcorrectionEq] at h
  dsimp only [beta, B] at hmain hquarterScaled hcorrectionScaled
  nlinarith only [h, hmain, hquarterScaled, hcorrectionScaled]

theorem nicolasPrimePowerTail_uniform_square_bias (hRH : RiemannHypothesis)
    {x : Real} (hx : 4 <= x) (hlog : 1 <= Real.log x) :
    abs (nicolasPrimePowerTail x -
      2 * x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) <=
      (10 + 40 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
        2 * Real.log (2 * Real.pi) + (Real.log 4 + 4) * (79 / 3 : Real)) *
          x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
  have hx1 : 1 < x := by linarith
  have hlpos : 0 < Real.log x := Real.log_pos hx1
  have hhigh := nicolasPrimePowerTail_higher_roots_bound (by linarith : 3 <= x) hlog
  have hsquare := nicolasPsiSquareTail_uniform_error hRH hx hlog
  have hkernel := nicolasHalfKernel_explicit_error hx1
  have hpow : (Real.log x) ^ 2 <= (Real.log x) ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_right hlog (sq_nonneg (Real.log x))]
  have hinv : Inv.inv ((Real.log x) ^ 3) <= Inv.inv ((Real.log x) ^ 2) := by
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hlpos 2) hpow
  have hscale : nicolasSpectralRemainderScale x <=
      5 * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hinv
      (show 0 <= 4 * x ^ (-(1 / 2 : Real)) by positivity)
    dsimp [nicolasSpectralRemainderScale]
    nlinarith only [h]
  have hsplit : nicolasPrimePowerTail x - 2 * x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) =
      (nicolasPrimePowerTail x - nicolasPsiRootTail 2 x) +
      (nicolasPsiRootTail 2 x - (robinZeroKernel 1 (1 / 2 : Complex) x).re) +
      ((robinZeroKernel 1 (1 / 2 : Complex) x).re -
        2 * x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) := by ring
  rw [hsplit]
  have htriangle := (abs_add_le
    ((nicolasPrimePowerTail x - nicolasPsiRootTail 2 x) +
      (nicolasPsiRootTail 2 x - (robinZeroKernel 1 (1 / 2 : Complex) x).re))
    ((robinZeroKernel 1 (1 / 2 : Complex) x).re -
      2 * x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x))).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_of_nonneg hhigh.1] at htriangle
  nlinarith only [htriangle, hhigh.2, hsquare, hkernel, hscale]

theorem nicolasK_wave_uniform_error (hRH : RiemannHypothesis)
    {x : Real} (hx : 4 <= x) (hlog : 1 <= Real.log x) :
    abs (nicolasK x + (2 + nicolasZeroWave x) /
        (x ^ (1 / 2 : Real) * Real.log x)) <=
      (10 + 45 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
        4 * Real.log (2 * Real.pi) + (Real.log 4 + 4) * (79 / 3 : Real)) *
          x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
  have hx3 : 3 <= x := by linarith
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := zero_lt_one.trans hx1
  have hKInt := nicolasThetaTail_integrableOn_Ioi_two.mono_set
    (Set.Ioi_subset_Ioi (show (2 : Real) <= x by linarith))
  have hJInt := nicolasPsiTail_integrableOn_Ioi_three.mono_set (Set.Ioi_subset_Ioi hx3)
  have hIdentity := nicolasJ_eq_K_add_primePowerTail hKInt hJInt
  have hK : nicolasK x = nicolasJ x - nicolasPrimePowerTail x := by linarith only [hIdentity]
  have hnorm : 2 * x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) =
      2 / (x ^ (1 / 2 : Real) * Real.log x) := by
    rw [Real.rpow_neg hxpos.le]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hsplit : nicolasK x + (2 + nicolasZeroWave x) /
      (x ^ (1 / 2 : Real) * Real.log x) =
      (nicolasJ x + nicolasZeroWave x / (x ^ (1 / 2 : Real) * Real.log x)) -
      (nicolasPrimePowerTail x - 2 * x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) := by
    rw [hK, hnorm]
    ring
  rw [hsplit]
  have htriangle := norm_sub_le
    (nicolasJ x + nicolasZeroWave x / (x ^ (1 / 2 : Real) * Real.log x))
    (nicolasPrimePowerTail x - 2 * x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x))
  simp only [Real.norm_eq_abs] at htriangle
  have hpsi := nicolasJ_wave_uniform_error hRH hx3 hlog
  have hpowers := nicolasPrimePowerTail_uniform_square_bias hRH hx hlog
  nlinarith only [htriangle, hpsi, hpowers]

end PrimeFactorOscillations
