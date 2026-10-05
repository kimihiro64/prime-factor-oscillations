/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasNegativeEnvelope

/-!
# The full spectral main term of the weighted psi tail

Retain the complete multiplicity-counted zero series instead of replacing it
by its absolute envelope. The explicit remainder is one logarithm smaller.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Robin1984

def nicolasSpectralAtom (rho : Complex) (x : Real) : Complex :=
  (x : Complex) ^ (rho - 1) / (rho * (1 - rho))

def nicolasSpectralTail (x : Real) : Complex :=
  tsum (fun p : RiemannXiDivisorZeroIndex => nicolasSpectralAtom (riemannXiDivisorZeroValue p) x)

def nicolasSpectralRemainderScale (x : Real) : Real :=
  x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) +
    4 * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 3)

theorem norm_nicolasSpectralAtom_le {rho : Complex} (hrho : Not (rho = 0))
    (hRe : rho.re = (1 / 2 : Real)) {x : Real} (hx : 1 < x) :
    norm (nicolasSpectralAtom rho x) <=
      (Inv.inv (norm rho)) ^ 2 * x ^ (-(1 / 2 : Real)) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hnorm : 0 < norm rho := norm_pos_iff.mpr hrho
  have hn : norm rho <= norm (1 - rho) := by
    calc
      norm rho <= norm (rho - (1 : Complex)) := by
        simpa only [Nat.cast_one] using norm_le_norm_sub_nat_of_re_eq_half
          (n := 1) (by norm_num) hRe
      _ = norm ((1 : Complex) - rho) := norm_sub_rev _ _
  have hden : (norm rho) ^ 2 <= norm rho * norm (1 - rho) := by
    nlinarith only [mul_le_mul_of_nonneg_left hn hnorm.le]
  have hexp : (rho - 1).re = -(1 / 2 : Real) := by
    simp only [Complex.sub_re, Complex.one_re, hRe]
    norm_num
  rw [nicolasSpectralAtom, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hexp]
  calc
    x ^ (-(1 / 2 : Real)) / (norm rho * norm (1 - rho)) <=
        x ^ (-(1 / 2 : Real)) / (norm rho) ^ 2 :=
      div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hxpos _).le (pow_pos hnorm 2) hden
    _ = (Inv.inv (norm rho)) ^ 2 * x ^ (-(1 / 2 : Real)) := by
      rw [div_eq_mul_inv, inv_pow]
      ring

theorem summable_nicolasSpectralAtom (hRH : RiemannHypothesis)
    {x : Real} (hx : 1 < x) :
    Summable (fun p : RiemannXiDivisorZeroIndex => nicolasSpectralAtom (riemannXiDivisorZeroValue p) x) := by
  have hMajor := summable_robinXiZeroWeight.mul_right (x ^ (-(1 / 2 : Real)))
  apply hMajor.of_norm_bounded
  intro p
  exact norm_nicolasSpectralAtom_le (riemannXiDivisorZeroValue_ne_zero p)
    (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p) hx

theorem norm_nicolasSpectralTail_le (hRH : RiemannHypothesis) {x : Real} (hx : 1 < x) :
    norm (nicolasSpectralTail x) <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) * x ^ (-(1 / 2 : Real)) := by
  have hs := (summable_nicolasSpectralAtom hRH hx).norm
  have hMajor := summable_robinXiZeroWeight.mul_right (x ^ (-(1 / 2 : Real)))
  calc
    norm (nicolasSpectralTail x) <=
        tsum (fun p : RiemannXiDivisorZeroIndex => norm (nicolasSpectralAtom (riemannXiDivisorZeroValue p) x)) :=
      norm_tsum_le_tsum_norm hs
    _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
        (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ 2 * x ^ (-(1 / 2 : Real))) := by
      apply hs.tsum_le_tsum _ hMajor
      intro p
      exact norm_nicolasSpectralAtom_le (riemannXiDivisorZeroValue_ne_zero p)
        (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p) hx
    _ = _ := by rw [tsum_mul_right, robinXiZeroConstant_eq_of_riemannHypothesis hRH]

theorem nicolasSpectral_kernel_split {rho : Complex}
    (hRe : rho.re = (1 / 2 : Real)) {x : Real} (hx : 1 < x) :
    robinZeroKernel 1 rho x / rho =
      nicolasSpectralAtom rho x / (Real.log x : Complex) +
        robinZeroKernelRemainder 1 rho x / rho := by
  rw [robinZeroKernel_eq_main_add_remainder (by norm_num) hx (by
    rw [hRe]
    norm_num)]
  simp only [nicolasSpectralAtom, Nat.cast_one, Complex.ofReal_inv,
    div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem nicolasJ_spectral_explicit_error (hRH : RiemannHypothesis)
    {x : Real} (hx : 3 <= x) :
    norm ((nicolasJ x : Complex) + nicolasSpectralTail x / (Real.log x : Complex)) <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        nicolasSpectralRemainderScale x +
      Real.log (2 * Real.pi) * x ^ (-(1 : Real)) * Inv.inv (Real.log x) := by
  have hx1 : 1 < x := by linarith
  have hx2 : 2 <= x := by linarith
  let R (p : RiemannXiDivisorZeroIndex) : Complex :=
    robinZeroKernelRemainder 1 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p
  have hp (p : RiemannXiDivisorZeroIndex) :
      norm (R p) <= (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ 2 *
        nicolasSpectralRemainderScale x := by
    have h := norm_robinZeroKernelRemainder_div_rho_le (n := 1) (by norm_num)
      (riemannXiDivisorZeroValue_ne_zero p)
      (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p) hx1
    dsimp [R, nicolasSpectralRemainderScale]
    convert h using 1
    norm_num
    ring
  have hm := summable_robinXiZeroWeight.mul_right (nicolasSpectralRemainderScale x)
  have hr : Summable R := hm.of_norm_bounded hp
  have hR : norm (tsum R) <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        nicolasSpectralRemainderScale x := by
    calc
      norm (tsum R) <= tsum (fun p => norm (R p)) := norm_tsum_le_tsum_norm hr.norm
      _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ 2 *
            nicolasSpectralRemainderScale x) := hr.norm.tsum_le_tsum hp hm
      _ = _ := by rw [tsum_mul_right, robinXiZeroConstant_eq_of_riemannHypothesis hRH]
  have hsplit : tsum (fun p : RiemannXiDivisorZeroIndex =>
      robinZeroKernel 1 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) =
      nicolasSpectralTail x / (Real.log x : Complex) + tsum R := by
    calc
      _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
          nicolasSpectralAtom (riemannXiDivisorZeroValue p) x / (Real.log x : Complex) + R p) := by
        apply tsum_congr
        intro p
        exact nicolasSpectral_kernel_split
          (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p) hx1
      _ = _ := by
        rw [((summable_nicolasSpectralAtom hRH hx1).div_const _).tsum_add hr, tsum_div_const]
        rfl
  have hJ := robinPsiWeightedErrorIntegral_one_eq_zero_sum_correction hRH hx2
  rw [<- nicolasJ_eq_weighted_error_one hx, hsplit] at hJ
  have hcorr := robinTrivialZeroCorrection_bounds (n := 1) (by norm_num) hx2
  calc
    norm ((nicolasJ x : Complex) + nicolasSpectralTail x / (Real.log x : Complex)) =
        norm (-tsum R - (robinTrivialZeroCorrection 1 x : Complex)) := by
      congr 1
      rw [hJ]
      ring
    _ <= norm (tsum R) + robinTrivialZeroCorrection 1 x := by
      have h := norm_sub_le (-tsum R) (robinTrivialZeroCorrection 1 x : Complex)
      simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcorr.1] using h
    _ <= _ := by
      have h := add_le_add hR hcorr.2
      simpa only [Nat.cast_one] using h

/-- The real normalized zero sum; an exact rescaling, retaining every zero. -/
def nicolasZeroWave (x : Real) : Real :=
  x ^ (1 / 2 : Real) * (nicolasSpectralTail x).re

theorem abs_nicolasZeroWave_le (hRH : RiemannHypothesis) {x : Real} (hx : 1 < x) :
    abs (nicolasZeroWave x) <= Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hp := Real.rpow_pos_of_pos hxpos (1 / 2 : Real)
  rw [nicolasZeroWave, abs_mul, abs_of_pos hp]
  calc
    x ^ (1 / 2 : Real) * abs (nicolasSpectralTail x).re <=
        x ^ (1 / 2 : Real) * norm (nicolasSpectralTail x) :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hp.le
    _ <= x ^ (1 / 2 : Real) *
        ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
          x ^ (-(1 / 2 : Real))) :=
      mul_le_mul_of_nonneg_left (norm_nicolasSpectralTail_le hRH hx) hp.le
    _ = Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
      rw [show x ^ (1 / 2 : Real) *
          ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
            x ^ (-(1 / 2 : Real))) =
          (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
            (x ^ (1 / 2 : Real) * x ^ (-(1 / 2 : Real))) by ring]
      rw [<- Real.rpow_add hxpos]
      norm_num

theorem nicolasJ_wave_explicit_error (hRH : RiemannHypothesis)
    {x : Real} (hx : 3 <= x) :
    abs (nicolasJ x + nicolasZeroWave x /
        (x ^ (1 / 2 : Real) * Real.log x)) <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        nicolasSpectralRemainderScale x +
      Real.log (2 * Real.pi) * x ^ (-(1 : Real)) * Inv.inv (Real.log x) := by
  have hx1 : 1 < x := by linarith
  have hp := Real.rpow_pos_of_pos (zero_lt_one.trans hx1) (1 / 2 : Real)
  have hlog := Real.log_pos hx1
  have hre : ((nicolasJ x : Complex) +
      nicolasSpectralTail x / (Real.log x : Complex)).re =
      nicolasJ x + (nicolasSpectralTail x).re / Real.log x := by
    rw [div_eq_mul_inv, <- Complex.ofReal_inv]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero, div_eq_mul_inv]
  have hscale : nicolasZeroWave x / (x ^ (1 / 2 : Real) * Real.log x) =
      (nicolasSpectralTail x).re / Real.log x := by
    dsimp [nicolasZeroWave]
    field_simp
  rw [hscale]
  have h := (Complex.abs_re_le_norm ((nicolasJ x : Complex) +
    nicolasSpectralTail x / (Real.log x : Complex))).trans
      (nicolasJ_spectral_explicit_error hRH hx)
  rwa [hre] at h

theorem nicolasZeroWave_eq_spectral_sum (hRH : RiemannHypothesis)
    {x : Real} (hx : 1 < x) :
    nicolasZeroWave x =
      (tsum (fun p : RiemannXiDivisorZeroIndex =>
        (x : Complex) ^ ((riemannXiDivisorZeroValue p).im * Complex.I) /
          (riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)))).re := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hxNe : Not ((x : Complex) = 0) := Complex.ofReal_ne_zero.mpr (ne_of_gt hxpos)
  have hsum : ((x ^ (1 / 2 : Real) : Real) : Complex) * nicolasSpectralTail x =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        (x : Complex) ^ ((riemannXiDivisorZeroValue p).im * Complex.I) /
          (riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p))) := by
    rw [nicolasSpectralTail, <- tsum_mul_left]
    apply tsum_congr
    intro p
    rw [nicolasSpectralAtom, <- mul_div_assoc, Complex.ofReal_cpow hxpos.le,
      <- Complex.cpow_add _ _ hxNe]
    have he : ((1 / 2 : Real) : Complex) + (riemannXiDivisorZeroValue p - 1) =
        (riemannXiDivisorZeroValue p).im * Complex.I := by
      apply Complex.ext
      . simp only [Complex.add_re, Complex.ofReal_re, Complex.sub_re, Complex.one_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, sub_zero,
          riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p]
        norm_num
      . simp
    rw [he]
  have h := congrArg Complex.re hsum
  simpa only [nicolasZeroWave, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using h

theorem nicolasJ_wave_uniform_error (hRH : RiemannHypothesis)
    {x : Real} (hx : 3 <= x) (hlog : 1 <= Real.log x) :
    abs (nicolasJ x + nicolasZeroWave x /
        (x ^ (1 / 2 : Real) * Real.log x)) <=
      (5 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
        2 * Real.log (2 * Real.pi)) *
          x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := zero_lt_one.trans hx1
  have hlpos : 0 < Real.log x := Real.log_pos hx1
  have hp := Real.rpow_pos_of_pos hxpos (1 / 2 : Real)
  have hm := Real.rpow_pos_of_pos hxpos (-(1 / 2 : Real))
  let beta := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  have hb : 0 <= beta := by
    have h := abs_nicolasZeroWave_le hRH hx1
    exact (abs_nonneg _).trans h
  have hK : 0 <= Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hpow : (Real.log x) ^ 2 <= (Real.log x) ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_right hlog (sq_nonneg (Real.log x))]
  have hinv : Inv.inv ((Real.log x) ^ 3) <= Inv.inv ((Real.log x) ^ 2) := by
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hlpos 2) hpow
  have hscale : nicolasSpectralRemainderScale x <=
      5 * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hinv (show 0 <= 4 * x ^ (-(1 / 2 : Real)) by positivity)
    dsimp [nicolasSpectralRemainderScale]
    nlinarith only [h]
  have hdiv : x ^ (-(1 / 2 : Real)) = x ^ (1 / 2 : Real) / x := by
    rw [show -(1 / 2 : Real) = 1 / 2 - 1 by norm_num,
      Real.rpow_sub hxpos, Real.rpow_one]
  have hlroot : Real.log x <= 2 * x ^ (1 / 2 : Real) := by
    have h := Real.log_le_sub_one_of_pos hp
    rw [Real.log_rpow hxpos] at h
    linarith only [h]
  have hcorrection : x ^ (-(1 : Real)) * Inv.inv (Real.log x) <=
      2 * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hlroot
      (show 0 <= Inv.inv x * Inv.inv ((Real.log x) ^ 2) by positivity)
    convert h using 1
    . rw [Real.rpow_neg hxpos.le, Real.rpow_one]
      field_simp
    . rw [hdiv]
      simp only [div_eq_mul_inv]
      ring
  have h := nicolasJ_wave_explicit_error hRH hx
  have h1 := mul_le_mul_of_nonneg_left hscale hb
  have h2 := mul_le_mul_of_nonneg_left hcorrection hK
  dsimp [beta] at h1
  nlinarith only [h, h1, h2]

end PrimeFactorOscillations
