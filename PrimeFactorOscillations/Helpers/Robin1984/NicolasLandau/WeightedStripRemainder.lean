/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors

Generalizes the maintained Robin1984 kernel estimates,
ported from bfa72aec0c25c8ee29cefe4449d778ff30412bee (Apache-2.0).
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedMellinKernel

/-!
# Remainder bounds retaining the zero's real part

For integer weights n >= 2, Re(rho) <= 1 suffices for the inverse-square
majorant. These estimates retain x^(Re(rho)-n) without assuming RH.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Robin1984
open Complex MeasureTheory Set

theorem norm_le_norm_sub_nat_of_re_le_one
    {n : Nat} (hn : 2 <= n) {rho : Complex}
    (hRe : rho.re <= 1) :
    norm rho <= norm (rho - (n : Complex)) := by
  apply le_of_sq_le_sq
  case h =>
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.natCast_re, Complex.natCast_im, sub_zero]
    have hnReal : (2 : Real) <= (n : Real) := by
      exact_mod_cast hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hnReal) (Nat.cast_nonneg n),
      mul_nonneg (sub_nonneg.mpr hRe) (Nat.cast_nonneg n)]
  case hb => exact norm_nonneg _

/-- The leading upper-strip coefficient has the same inverse-square zero
majorant as the remainder. -/
theorem norm_nat_div_sub_div_le_strip_weight
    {n : Nat} (hn : 2 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) (hRe : rho.re <= 1) :
    norm (((n : Complex) / ((n : Complex) - rho)) / rho) <=
      (n : Real) * (Inv.inv (norm rho)) ^ (2 : Nat) := by
  have hNormLe : norm rho <= norm (rho - (n : Complex)) :=
    norm_le_norm_sub_nat_of_re_le_one hn hRe
  have hOppNorm :
      norm ((n : Complex) - rho) = norm (rho - (n : Complex)) := by
    rw [show (n : Complex) - rho = -(rho - (n : Complex)) by ring,
      norm_neg]
  have hNormPos : 0 < norm rho := norm_pos_iff.mpr hRho
  have hInvLe :
      Inv.inv (norm ((n : Complex) - rho)) <= Inv.inv (norm rho) := by
    rw [hOppNorm]
    simpa [one_div] using one_div_le_one_div_of_le hNormPos hNormLe
  rw [norm_div, norm_div, Complex.norm_natCast]
  calc
    (n : Real) / norm ((n : Complex) - rho) / norm rho =
        (n : Real) * Inv.inv (norm ((n : Complex) - rho)) *
          Inv.inv (norm rho) := by ring
    _ <= (n : Real) * Inv.inv (norm rho) * Inv.inv (norm rho) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hInvLe (Nat.cast_nonneg n))
        (inv_nonneg.mpr (norm_nonneg rho))
    _ = (n : Real) * (Inv.inv (norm rho)) ^ (2 : Nat) := by
      ring


theorem norm_robinZeroKernelRemainder_div_rho_le_re
    {n : Nat} (hn : 2 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) (hRe : rho.re <= 1)
    {x : Real} (hx : 1 < x) :
    norm (robinZeroKernelRemainder n rho x / rho) <=
      (Inv.inv (norm rho)) ^ (2 : Nat) *
        (x ^ (rho.re - (n : Real)) *
            Inv.inv ((Real.log x) ^ (2 : Nat)) +
          2 *
            ((-x ^ (rho.re - (n : Real)) /
                  (rho.re - (n : Real))) *
              Inv.inv ((Real.log x) ^ (3 : Nat)))) := by
  have hNormLe : norm rho <= norm (rho - (n : Complex)) :=
    norm_le_norm_sub_nat_of_re_le_one hn hRe
  have hNormPos : 0 < norm rho := norm_pos_iff.mpr hRho
  have hNormSqPos : 0 < (norm rho) ^ (2 : Nat) :=
    pow_pos hNormPos 2
  have hNormSqLe :
      (norm rho) ^ (2 : Nat) <=
        (norm (rho - (n : Complex))) ^ (2 : Nat) := by
    nlinarith [norm_nonneg (rho - (n : Complex))]
  have hInvNormLe :
      norm (Inv.inv ((rho - (n : Complex)) ^ (2 : Nat))) <=
        (Inv.inv (norm rho)) ^ (2 : Nat) := by
    rw [norm_inv, norm_pow]
    simpa [one_div, inv_pow] using
      one_div_le_one_div_of_le hNormSqPos hNormSqLe
  have hBracket :=
    norm_robinZeroKernelRemainder_bracket_le_re hx
      (show rho.re < (n : Real) by
        have hnReal : (2 : Real) <= n := by exact_mod_cast hn
        linarith)
  rw [robinZeroKernelRemainder_div_rho hRho, norm_mul]
  simpa only [mul_assoc] using mul_le_mul hInvNormLe hBracket (norm_nonneg _)
    (pow_nonneg (inv_nonneg.mpr (norm_nonneg rho)) 2)


theorem norm_robinZeroKernel_div_rho_le_re_weight
    {n : Nat} (hn : 2 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) (hRe : rho.re <= 1)
    {x : Real} (hx : 1 < x) :
    norm (robinZeroKernel n rho x / rho) <=
      (Inv.inv (norm rho)) ^ (2 : Nat) *
        ((n : Real) * x ^ (rho.re - (n : Real)) *
            Inv.inv (Real.log x) +
          (x ^ (rho.re - (n : Real)) *
              Inv.inv ((Real.log x) ^ (2 : Nat)) +
            2 *
              ((-x ^ (rho.re - (n : Real)) /
                    (rho.re - (n : Real))) *
                Inv.inv ((Real.log x) ^ (3 : Nat))))) := by
  have hReLt : rho.re < (n : Real) := by
    have hnReal : (2 : Real) <= (n : Real) := by
      exact_mod_cast hn
    linarith
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  have hCoefficient :=
    norm_nat_div_sub_div_le_strip_weight hn hRho hRe
  have hFactorNorm :
      norm
          ((x : Complex) ^ (rho - (n : Complex)) *
            (((Inv.inv (Real.log x) : Real) : Complex))) =
        x ^ (rho.re - (n : Real)) * Inv.inv (Real.log x) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_trans Real.zero_lt_one hx), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hLogPos)]
    simp only [Complex.sub_re, Complex.natCast_re]
  have hMain :
      norm
          ((((n : Complex) / ((n : Complex) - rho)) *
              (x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) / rho) <=
        (Inv.inv (norm rho)) ^ (2 : Nat) *
          ((n : Real) * x ^ (rho.re - (n : Real)) *
            Inv.inv (Real.log x)) := by
    have hRewrite :
        (((n : Complex) / ((n : Complex) - rho)) *
              (x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) / rho =
          (((n : Complex) / ((n : Complex) - rho)) / rho) *
            ((x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) := by
      ring
    rw [hRewrite, norm_mul, hFactorNorm]
    have hFactorNonneg :
        0 <= x ^ (rho.re - (n : Real)) * Inv.inv (Real.log x) :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans Real.zero_lt_one hx)) _)
        (inv_nonneg.mpr hLogPos.le)
    calc
      norm (((n : Complex) / ((n : Complex) - rho)) / rho) *
          (x ^ (rho.re - (n : Real)) * Inv.inv (Real.log x)) <=
        ((n : Real) * (Inv.inv (norm rho)) ^ (2 : Nat)) *
          (x ^ (rho.re - (n : Real)) * Inv.inv (Real.log x)) :=
        mul_le_mul_of_nonneg_right hCoefficient hFactorNonneg
      _ = (Inv.inv (norm rho)) ^ (2 : Nat) *
          ((n : Real) * x ^ (rho.re - (n : Real)) *
            Inv.inv (Real.log x)) := by ring
  have hRemainder :=
    norm_robinZeroKernelRemainder_div_rho_le_re hn hRho hRe hx
  rw [robinZeroKernel_eq_main_add_remainder (by omega : 1 <= n) hx hReLt, add_div]
  calc
    norm
        ((((n : Complex) / ((n : Complex) - rho)) *
              (x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) / rho +
          robinZeroKernelRemainder n rho x / rho) <=
        norm
            ((((n : Complex) / ((n : Complex) - rho)) *
                (x : Complex) ^ (rho - (n : Complex)) *
                (((Inv.inv (Real.log x) : Real) : Complex))) / rho) +
          norm (robinZeroKernelRemainder n rho x / rho) :=
      norm_add_le _ _
    _ <= (Inv.inv (norm rho)) ^ (2 : Nat) *
          ((n : Real) * x ^ (rho.re - (n : Real)) *
            Inv.inv (Real.log x)) +
        (Inv.inv (norm rho)) ^ (2 : Nat) *
          (x ^ (rho.re - (n : Real)) *
              Inv.inv ((Real.log x) ^ (2 : Nat)) +
            2 *
              ((-x ^ (rho.re - (n : Real)) /
                    (rho.re - (n : Real))) *
                Inv.inv ((Real.log x) ^ (3 : Nat)))) :=
      add_le_add hMain hRemainder
    _ = _ := by ring

theorem negative_rpow_tail_mono {x s b : Real} (hx : 1 < x)
    (hs : s <= b) (hb : b < 0) :
    -x ^ s / s <= -x ^ b / b := by
  have hPow := Real.rpow_le_rpow_of_exponent_le hx.le hs
  have hInv := one_div_le_one_div_of_le (neg_pos.mpr hb) (neg_le_neg hs)
  have hsNeg : s < 0 := lt_of_le_of_lt hs hb
  calc
    -x ^ s / s = x ^ s * (1 / -s) := by ring
    _ <= x ^ b * (1 / -b) :=
      mul_le_mul hPow hInv (le_of_lt (one_div_pos.mpr (neg_pos.mpr hsNeg)))
        (Real.rpow_nonneg (by linarith) _)
    _ = -x ^ b / b := by ring

def robinStripKernelMajorant (b : Real) (n : Nat) (x : Real) : Real :=
  (n : Real) * x ^ (b - (n : Real)) * Inv.inv (Real.log x) +
    (x ^ (b - (n : Real)) * Inv.inv ((Real.log x) ^ (2 : Nat)) +
      2 * (-x ^ (b - (n : Real)) / (b - (n : Real))) *
        Inv.inv ((Real.log x) ^ (3 : Nat)))

theorem norm_robinZeroKernel_div_rho_le_strip
    {n : Nat} (hn : 2 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) {b : Real} (hRe : rho.re <= b) (hb : b <= 1)
    {x : Real} (hx : 1 < x) :
    norm (robinZeroKernel n rho x / rho) <=
      (Inv.inv (norm rho)) ^ (2 : Nat) * robinStripKernelMajorant b n x := by
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hPow : x ^ (rho.re - (n : Real)) <= x ^ (b - (n : Real)) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (sub_le_sub_right hRe _)
  have hTail := negative_rpow_tail_mono hx (sub_le_sub_right hRe (n : Real))
    (show b - (n : Real) < 0 by linarith)
  have hLog : 0 <= Real.log x := (Real.log_pos hx).le
  have hMain := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hPow (Nat.cast_nonneg n)) (inv_nonneg.mpr hLog)
  have hSquare := mul_le_mul_of_nonneg_right hPow
    (inv_nonneg.mpr (pow_nonneg hLog 2))
  have hCube := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hTail (by norm_num : (0 : Real) <= 2))
    (inv_nonneg.mpr (pow_nonneg hLog 3))
  apply (norm_robinZeroKernel_div_rho_le_re_weight hn hRho (le_trans hRe hb) hx).trans
  dsimp only [robinStripKernelMajorant]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg (Inv.inv (norm rho)))
  simpa only [mul_assoc] using add_le_add hMain (add_le_add hSquare hCube)

theorem integrableOn_robinStripKernelMajorant_two {b x : Real}
    (hb : b < 1) (hx : 1 < x) :
    IntegrableOn (robinStripKernelMajorant b 2) (Ioi x) := by
  have hTerm (k : Nat) : IntegrableOn (fun t : Real =>
      t ^ (b - 2) * Inv.inv ((Real.log t) ^ k)) (Ioi x) := by
    have hRaw := (integrableOn_cpow_div_log_pow
      (a := ((b - 2 : Real) : Complex)) hx (by simp; linarith) k).norm
    apply IntegrableOn.congr_fun hRaw _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_trans Real.zero_lt_one (lt_trans hx ht)), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (Real.log_pos (lt_trans hx ht)).le k))]
    simp
  have hRaw := ((hTerm 1).const_mul 2).add
    ((hTerm 2).add ((hTerm 3).const_mul (-(2 / (b - 2)))))
  apply IntegrableOn.congr_fun hRaw _ measurableSet_Ioi
  intro t ht
  simp only [robinStripKernelMajorant, Nat.cast_ofNat, pow_one, Pi.add_apply]
  ring

end Robin1984
