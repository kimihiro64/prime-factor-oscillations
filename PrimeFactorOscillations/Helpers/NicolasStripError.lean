/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasStripZeroSum
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedStripEndpoint

/-!
# Nicolas' arithmetic integral with a complete strip spectral error

The full signed spectral term is retained. A reciprocal-product estimate
bounds the twice-integrated remainder using the unconditional zero-product
sum, with an explicit factor 1 / (1 - b). The strip hypothesis is not proved
here; the conclusion applies when all canonical zeros lie in [1 - b, b].
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Complex MeasureTheory Set Robin1984

theorem strip_shift_inverse_square_le {b : Real} (hb : 0 < b) (hbOne : b < 1)
    {rho : Complex} (hLower : 1 - b <= rho.re) (hUpper : rho.re <= b) :
    norm (Inv.inv ((rho - 1) ^ (2 : Nat))) <=
      ((rho * (1 - rho)) ^ (-1 : Int)).re / (1 - b) := by
  have hq : 0 < 1 - b := by linarith
  have ha : 0 < rho.re := by linarith
  have haOne : rho.re < 1 := by linarith
  have hRho : Not (rho = 0) := by
    intro h
    simp only [h, Complex.zero_re] at ha
    linarith
  have hOne : Not (1 - rho = 0) := by
    intro h
    have h := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h
    linarith
  have hA : 0 < Complex.normSq rho := by
    rw [<- Complex.sq_norm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hRho)
  have hB : 0 < Complex.normSq (1 - rho) := by
    rw [<- Complex.sq_norm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hOne)
  have hP : 0 < Complex.normSq (rho * (1 - rho)) := by
    rw [Complex.normSq_mul]
    exact mul_pos hA hB
  have hCompare : (1 - b) * Complex.normSq rho <= (rho * (1 - rho)).re := by
    have haa : rho.re ^ 2 <= rho.re := by
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr haOne.le)]
    have hFirst := mul_le_mul_of_nonneg_left haa hq.le
    have hSecond : (1 - b) * rho.im ^ 2 <= rho.im ^ 2 := by
      nlinarith [mul_nonneg hb.le (sq_nonneg rho.im)]
    have hThird := mul_nonneg (sub_nonneg.mpr hUpper) ha.le
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.sub_re,
      Complex.one_re, Complex.sub_im, Complex.one_im]
    nlinarith only [hFirst, hSecond, hThird]
  have hShift : norm (rho - 1) ^ (2 : Nat) = Complex.normSq (1 - rho) := by
    rw [show rho - 1 = -(1 - rho) by ring, norm_neg, Complex.sq_norm]
  rw [norm_inv, norm_pow, hShift, zpow_neg_one, Complex.inv_re]
  have hLeft : (Complex.normSq (1 - rho)) ^ (-1 : Int) *
      (Complex.normSq (rho * (1 - rho)) * (1 - b)) =
      (1 - b) * Complex.normSq rho := by
    rw [zpow_neg_one, Complex.normSq_mul]
    field_simp
  have hRight : ((rho * (1 - rho)).re / Complex.normSq (rho * (1 - rho)) /
      (1 - b)) * (Complex.normSq (rho * (1 - rho)) * (1 - b)) =
      (rho * (1 - rho)).re := by
    field_simp [hq.ne']
  by_contra hNot
  have hStrict := mul_lt_mul_of_pos_right (lt_of_not_ge hNot) (mul_pos hP hq)
  rw [hRight, <- zpow_neg_one, hLeft] at hStrict
  exact (not_lt_of_ge hCompare) hStrict

def nicolasStripRemainderScale (b x : Real) : Real :=
  x ^ (b - 1) * Inv.inv ((Real.log x) ^ 2) +
    2 * ((-x ^ (b - 1) / (b - 1)) * Inv.inv ((Real.log x) ^ 3))

theorem norm_robinZeroKernelRemainder_one_div_strip_le
    {b : Real} (hb : 0 < b) (hbOne : b < 1) {rho : Complex}
    (hRho : Not (rho = 0)) (hLower : 1 - b <= rho.re) (hUpper : rho.re <= b)
    {x : Real} (hx : 1 < x) :
    norm (robinZeroKernelRemainder 1 rho x / rho) <=
      (((rho * (1 - rho)) ^ (-1 : Int)).re / (1 - b)) *
        nicolasStripRemainderScale b x := by
  have hCoeff := strip_shift_inverse_square_le hb hbOne hLower hUpper
  have hRe : rho.re < 1 := lt_of_le_of_lt hUpper hbOne
  have hBracket := norm_robinZeroKernelRemainder_bracket_le_re (n := 1) (s := rho) hx
    (by simpa only [Nat.cast_one] using hRe)
  simp only [Nat.cast_one] at hBracket
  have hPow := Real.rpow_le_rpow_of_exponent_le hx.le (sub_le_sub_right hUpper 1)
  have hTail := negative_rpow_tail_mono hx (sub_le_sub_right hUpper 1)
    (show b - 1 < 0 by linarith)
  have hLog : 0 <= Real.log x := (Real.log_pos hx).le
  have hBracketBound := add_le_add
    (mul_le_mul_of_nonneg_right hPow (inv_nonneg.mpr (pow_nonneg hLog 2)))
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hTail (inv_nonneg.mpr (pow_nonneg hLog 3)))
      (by norm_num : (0 : Real) <= 2))
  rw [robinZeroKernelRemainder_div_rho hRho, norm_mul]
  simp only [Nat.cast_one]
  exact mul_le_mul hCoeff (hBracket.trans hBracketBound) (norm_nonneg _)
    (le_trans (norm_nonneg _) hCoeff)

theorem nicolasSpectral_kernel_split_strip {rho : Complex}
    (hRe : rho.re < 1) {x : Real} (hx : 1 < x) :
    robinZeroKernel 1 rho x / rho =
      nicolasSpectralAtom rho x / (Real.log x : Complex) +
        robinZeroKernelRemainder 1 rho x / rho := by
  rw [robinZeroKernel_eq_main_add_remainder (by norm_num) hx (by simpa using hRe)]
  simp only [nicolasSpectralAtom, Nat.cast_one, Complex.ofReal_inv,
    div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem nicolasJ_spectral_explicit_error_strip {b : Real}
    (hb : 0 < b) (hbOne : b < 1)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      1 - b <= (riemannXiDivisorZeroValue p).re /\
        (riemannXiDivisorZeroValue p).re <= b)
    {x : Real} (hx : 3 <= x) :
    norm ((nicolasJ x : Complex) + nicolasSpectralTail x / (Real.log x : Complex)) <=
      ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) / (1 - b)) *
        nicolasStripRemainderScale b x +
      Real.log (2 * Real.pi) * x ^ (-(1 : Real)) * Inv.inv (Real.log x) := by
  have hx1 : 1 < x := by linarith
  have hx2 : 2 <= x := by linarith
  let R (p : RiemannXiDivisorZeroIndex) : Complex :=
    robinZeroKernelRemainder 1 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p
  have hsInv := summable_inverse_zero_product_strip hb hbOne hStrip
  have hsRe : Summable (fun p : RiemannXiDivisorZeroIndex =>
      ((riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int)).re) := by
    apply hsInv.norm.of_norm_bounded
    intro p
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm
      ((riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int))
  have hReSum : tsum (fun p : RiemannXiDivisorZeroIndex =>
      ((riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int)).re) =
      Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
    have hMap := Complex.reCLM.map_tsum hsInv
    rw [nicolas_inverse_zero_product_sum] at hMap
    simpa using hMap.symm
  have hp (p : RiemannXiDivisorZeroIndex) :
      norm (R p) <=
        (((riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int)).re /
          (1 - b)) * nicolasStripRemainderScale b x :=
    norm_robinZeroKernelRemainder_one_div_strip_le hb hbOne
      (riemannXiDivisorZeroValue_ne_zero p) (hStrip p).1 (hStrip p).2 hx1
  have hm := (hsRe.div_const (1 - b)).mul_right (nicolasStripRemainderScale b x)
  have hr : Summable R := hm.of_norm_bounded hp
  have hR : norm (tsum R) <=
      ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) / (1 - b)) *
        nicolasStripRemainderScale b x := by
    calc
      norm (tsum R) <= tsum (fun p => norm (R p)) := norm_tsum_le_tsum_norm hr.norm
      _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
          (((riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int)).re /
            (1 - b)) *
            nicolasStripRemainderScale b x) := hr.norm.tsum_le_tsum hp hm
      _ = _ := by rw [tsum_mul_right, tsum_div_const, hReSum]
  have hsplit : tsum (fun p : RiemannXiDivisorZeroIndex =>
      robinZeroKernel 1 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) =
      nicolasSpectralTail x / (Real.log x : Complex) + tsum R := by
    calc
      _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
          nicolasSpectralAtom (riemannXiDivisorZeroValue p) x / (Real.log x : Complex) + R p) := by
        apply tsum_congr
        intro p
        exact nicolasSpectral_kernel_split_strip (lt_of_le_of_lt (hStrip p).2 hbOne) hx1
      _ = _ := by
        rw [((summable_nicolasSpectralAtom_strip hb hbOne hStrip hx1).div_const _).tsum_add hr, tsum_div_const]
        rfl
  have hJ := robinPsiWeightedErrorIntegral_one_eq_zero_sum_correction_strip hbOne (fun p => (hStrip p).2) hx2
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


theorem nicolasJ_strip_envelope {b : Real}
    (hb : 0 < b) (hbOne : b < 1)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      1 - b <= (riemannXiDivisorZeroValue p).re /\
        (riemannXiDivisorZeroValue p).re <= b)
    {x : Real} (hx : 3 <= x) :
    abs (nicolasJ x) <=
      ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) /
        (2 * Real.sqrt (b * (1 - b)))) *
          x ^ (b - 1) * Inv.inv (Real.log x) +
      ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) / (1 - b)) *
        nicolasStripRemainderScale b x +
      Real.log (2 * Real.pi) * x ^ (-(1 : Real)) * Inv.inv (Real.log x) := by
  have hxOne : 1 < x := by linarith
  have hLog : 0 < Real.log x := Real.log_pos hxOne
  have hError := nicolasJ_spectral_explicit_error_strip hb hbOne hStrip hx
  have hSpectral := norm_nicolasSpectralTail_strip_le hb hbOne hStrip hxOne
  have hMain : norm (nicolasSpectralTail x / (Real.log x : Complex)) <=
      ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) /
        (2 * Real.sqrt (b * (1 - b)))) *
          x ^ (b - 1) * Inv.inv (Real.log x) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLog, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hSpectral (inv_nonneg.mpr hLog.le)
  have hTriangle := norm_sub_le
    ((nicolasJ x : Complex) + nicolasSpectralTail x / (Real.log x : Complex))
    (nicolasSpectralTail x / (Real.log x : Complex))
  rw [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs] at hTriangle
  have hBound := hTriangle.trans (add_le_add hError hMain)
  linarith only [hBound]

end PrimeFactorOscillations
