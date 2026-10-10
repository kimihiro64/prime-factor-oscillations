/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasStripSpectral

/-!
# The reciprocal-zero sum and a strip-uniform spectral estimate

Hadamard factorization gives the exact reciprocal-zero sum without RH.
The strip cone then controls the complete absolutely convergent spectral
series with the explicit endpoint constant used in the Nicolas transfer.
The zero-location hypothesis remains explicit; no zero-free region is
established by this module.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Complex Robin1984

theorem nicolas_inverse_zero_product_sum :
    tsum (fun p : RiemannXiDivisorZeroIndex =>
      (riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int)) =
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) : Real) := by
  choose P hDegree hFactorization using riemannXi_hadamard_factorization_no_monomial
  have hZeroAway (p : RiemannXiDivisorZeroIndex) :
      Not ((0 : Complex) = riemannXiDivisorZeroValue p) :=
    (riemannXiDivisorZeroValue_ne_zero p).symm
  have hOneAway (p : RiemannXiDivisorZeroIndex) :
      Not ((1 : Complex) = riemannXiDivisorZeroValue p) := by
    intro h
    have hXi := riemannXiDivisorZeroValue_eq_zero p
    rw [<- h, riemannXi_one_eq_half] at hXi
    norm_num at hXi
  have hAtZero := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
    hFactorization hZeroAway
  have hAtOne := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
    hFactorization hOneAway
  have hZeroSum : tsum (fun p : RiemannXiDivisorZeroIndex =>
      1 / (0 - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p) = 0 := by
    simp
  have hOneSum : tsum (fun p : RiemannXiDivisorZeroIndex =>
      1 / (1 - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p) =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        (riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int)) := by
    apply tsum_congr
    intro p
    have hr := riemannXiDivisorZeroValue_ne_zero p
    have ho : Not (1 - riemannXiDivisorZeroValue p = 0) := by
      intro h
      exact hOneAway p (sub_eq_zero.mp h)
    rw [zpow_neg_one]
    field_simp
    ring
  change logDeriv riemannXi 0 = P.derivative.eval 0 + _ at hAtZero
  change logDeriv riemannXi 1 = P.derivative.eval 1 + _ at hAtOne
  rw [hZeroSum, add_zero] at hAtZero
  rw [hOneSum, Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one hDegree]
    at hAtOne
  rw [logDeriv_riemannXi_one_eq_neg_zero, <- hAtZero] at hAtOne
  have hSum : tsum (fun p : RiemannXiDivisorZeroIndex =>
      (riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int)) =
      -2 * logDeriv riemannXi 0 := by linear_combination -hAtOne
  rw [hSum, neg_two_mul_logDeriv_riemannXi_zero_eq]
  push_cast
  rfl

theorem norm_inverse_zero_product_strip_coarse {b : Real}
    (hb : 0 < b) (hbOne : b < 1) {rho : Complex}
    (hLower : 1 - b <= rho.re) (hUpper : rho.re <= b) :
    norm ((rho * (1 - rho)) ^ (-1 : Int)) <=
      (1 - b) ^ (-1 : Int) * (Inv.inv (norm rho)) ^ 2 := by
  have hRe : 0 < rho.re := by linarith
  have hReOne : rho.re < 1 := by linarith
  have hRho : Not (rho = 0) := by
    intro h
    simp only [h, Complex.zero_re] at hRe
    exact (lt_irrefl 0) hRe
  have hn : 0 < norm rho := norm_pos_iff.mpr hRho
  have hPositive : 0 < (1 - b) * (norm rho) ^ 2 := by positivity
  have hProduct : (1 - b) * (norm rho) ^ 2 <= norm (rho * (1 - rho)) := by
    apply le_trans _ (Complex.re_le_norm _)
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    have hA := mul_nonneg hRe.le (sub_nonneg.mpr hUpper)
    have hB := mul_nonneg (sub_nonneg.mpr hbOne.le)
      (mul_nonneg hRe.le (sub_nonneg.mpr hReOne.le))
    have hC := mul_nonneg hb.le (sq_nonneg rho.im)
    nlinarith only [hA, hB, hC]
  rw [zpow_neg_one, norm_inv]
  calc
    _ <= 1 / ((1 - b) * (norm rho) ^ 2) := by
      simpa only [one_div] using div_le_div_of_nonneg_left
        (show (0 : Real) <= 1 by norm_num) hPositive hProduct
    _ = _ := by rw [zpow_neg_one, div_eq_mul_inv, mul_inv, inv_pow]; ring

theorem summable_inverse_zero_product_strip {b : Real}
    (hb : 0 < b) (hbOne : b < 1)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      1 - b <= (riemannXiDivisorZeroValue p).re /\
        (riemannXiDivisorZeroValue p).re <= b) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      (riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int)) := by
  apply (summable_robinXiZeroWeight.mul_left ((1 - b) ^ (-1 : Int))).of_norm_bounded
  intro p
  exact norm_inverse_zero_product_strip_coarse hb hbOne (hStrip p).1 (hStrip p).2

theorem summable_nicolasSpectralAtom_strip {b : Real}
    (hb : 0 < b) (hbOne : b < 1)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      1 - b <= (riemannXiDivisorZeroValue p).re /\
        (riemannXiDivisorZeroValue p).re <= b)
    {x : Real} (hx : 1 < x) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      nicolasSpectralAtom (riemannXiDivisorZeroValue p) x) := by
  have hs := (summable_inverse_zero_product_strip hb hbOne hStrip).norm.mul_left (x ^ (b - 1))
  apply hs.of_norm_bounded
  intro p
  rw [nicolasSpectralAtom, div_eq_mul_inv, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
  simp only [Complex.sub_re, Complex.one_re, zpow_neg_one]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [(hStrip p).2]))
    (norm_nonneg _)

theorem norm_nicolasSpectralTail_strip_le {b : Real}
    (hb : 0 < b) (hbOne : b < 1)
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      1 - b <= (riemannXiDivisorZeroValue p).re /\
        (riemannXiDivisorZeroValue p).re <= b)
    {x : Real} (hx : 1 < x) :
    norm (nicolasSpectralTail x) <=
      ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) /
        (2 * Real.sqrt (b * (1 - b)))) * x ^ (b - 1) := by
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
  have hsAtom := summable_nicolasSpectralAtom_strip hb hbOne hStrip hx
  have hsMajor := (hsRe.div_const (2 * Real.sqrt (b * (1 - b)))).mul_left (x ^ (b - 1))
  calc
    norm (nicolasSpectralTail x) <=
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          norm (nicolasSpectralAtom (riemannXiDivisorZeroValue p) x)) :=
      norm_tsum_le_tsum_norm hsAtom.norm
    _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
        x ^ (b - 1) *
          (((riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int)).re /
            (2 * Real.sqrt (b * (1 - b))))) := by
      apply hsAtom.norm.tsum_le_tsum _ hsMajor
      intro p
      exact norm_nicolasSpectralAtom_strip_le hb hbOne (hStrip p).1 (hStrip p).2 hx
    _ = _ := by rw [tsum_mul_left, tsum_div_const, hReSum]; ring

end PrimeFactorOscillations
