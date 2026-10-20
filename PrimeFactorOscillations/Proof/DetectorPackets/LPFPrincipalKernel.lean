/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.LPFPrincipalWeighted
import PrimeFactorOscillations.Helpers.NicolasZetaStrip
import PrimeFactorOscillations.Helpers.QRHSevenEighths
import PrimeFactorOscillations.Helpers.Robin1984.Analytic.XiSummability
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedMellinKernel
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedStripExplicit

/-!
# LPFPrincipalKernel

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Principal smoothed zero-kernel bounds below a fixed vertical line

This retains the complete Robin cutoff kernel, including its logarithmic
remainder. It is the zero-sum estimate for a principal prime-count transfer.
-/


namespace Robin1984

private theorem norm_sub_two_ge {s : Complex} (hs : s.re <= 1) :
    norm s <= norm (s - 2) := by
  have hSq : norm s ^ 2 <= norm (s - 2) ^ 2 := by
    rw [<- Complex.normSq_eq_norm_sq, <- Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    norm_num
    nlinarith
  nlinarith [norm_nonneg s, norm_nonneg (s - 2)]

/-- No critical-line hypothesis is used in this complete kernel estimate. -/
theorem norm_robinZeroKernel_two_le_of_re_le
    {alpha : Real} (hAlpha : alpha <= 1) {s : Complex}
    (hs : s.re <= alpha) (hsZero : Not (s = 0))
    {x : Real} (hx : 1 < x) (hLog : 1 <= Real.log x) :
    norm (robinZeroKernel 2 s x / s) <=
      5 * (x ^ (alpha - 2) * Inv.inv (Real.log x)) *
        (Inv.inv (norm s)) ^ (2 : Nat) := by
  have hsOne : s.re <= 1 := hs.trans hAlpha
  have hNorm := norm_sub_two_ge hsOne
  have hNormPos : 0 < norm s := norm_pos_iff.mpr hsZero
  have hInv : Inv.inv (norm (s - 2)) <= Inv.inv (norm s) := by
    have h := one_div_le_one_div_of_le hNormPos hNorm
    simpa only [one_div] using h
  have hInvSq : (Inv.inv (norm (s - 2))) ^ (2 : Nat) <=
      (Inv.inv (norm s)) ^ (2 : Nat) := by
    nlinarith [inv_nonneg.mpr (norm_nonneg (s - 2)),
      inv_nonneg.mpr (norm_nonneg s)]
  let X : Real := x ^ (s.re - 2)
  let Y : Real := x ^ (alpha - 2)
  let l : Real := Inv.inv (Real.log x)
  let R : Real := (Inv.inv (norm s)) ^ (2 : Nat)
  let T : Real := (Inv.inv (norm (s - 2))) ^ (2 : Nat)
  have hX : 0 <= X := Real.rpow_nonneg (by linarith) _
  have hXY : X <= Y :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hl : 0 <= l := inv_nonneg.mpr (by linarith)
  have hlOne : l <= 1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hLog
    simpa [l] using h
  have hlSq : l ^ (2 : Nat) <= l := by nlinarith
  have hlCube : l ^ (3 : Nat) <= l := by
    calc
      _ = l ^ (2 : Nat) * l := by ring
      _ <= l * l := mul_le_mul_of_nonneg_right hlSq hl
      _ = l ^ (2 : Nat) := by ring
      _ <= l := hlSq
  have hGap : 1 <= 2 - s.re := by linarith
  have hGapInv : Inv.inv (2 - s.re) <= 1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hGap
    simpa using h
  have hRatio : -X / (s.re - 2) <= X := by
    calc
      _ = X * Inv.inv (2 - s.re) := by
        rw [show s.re - 2 = -(2 - s.re) by ring, div_neg, div_eq_mul_inv]
        ring
      _ <= X * 1 := mul_le_mul_of_nonneg_left hGapInv hX
      _ = X := by ring
  have hR : 0 <= R := sq_nonneg _
  have hT : 0 <= T := sq_nonneg _
  have hTR : T <= R := hInvSq
  have hMain : X * l * (R + T) <= 2 * X * l * R := by
    calc
      _ <= X * l * (R + R) :=
        mul_le_mul_of_nonneg_left (by linarith : R + T <= R + R) (mul_nonneg hX hl)
      _ = _ := by ring
  have hRemCoeff : X * l ^ (2 : Nat) +
      2 * (-X / (s.re - 2)) * l ^ (3 : Nat) <= 3 * X * l := by
    have hFirst := mul_le_mul_of_nonneg_left hlSq hX
    have hRatioTerm := mul_le_mul_of_nonneg_right hRatio (by positivity : 0 <= 2 * l ^ (3 : Nat))
    have hCubeTerm := mul_le_mul_of_nonneg_left hlCube (by positivity : 0 <= 2 * X)
    nlinarith
  have hRem : (X * l ^ (2 : Nat) +
      2 * (-X / (s.re - 2)) * l ^ (3 : Nat)) * T <= 3 * X * l * R := by
    calc
      _ <= (3 * X * l) * T := mul_le_mul_of_nonneg_right hRemCoeff hT
      _ <= (3 * X * l) * R := mul_le_mul_of_nonneg_left hTR (by positivity)
  have hBound := norm_robinZeroKernel_div_le_inverseSquares
    (n := 2) (by decide) hsZero hx (by norm_num; linarith)
  norm_num only [Nat.cast_ofNat] at hBound
  have hFull : norm (robinZeroKernel 2 s x / s) <=
      X * l * (R + T) + (X * l ^ (2 : Nat) +
        2 * (-X / (s.re - 2)) * l ^ (3 : Nat)) * T := by
    simpa only [X, l, R, T, one_mul, <- inv_pow, mul_assoc] using hBound
  calc
    _ <= 2 * X * l * R + 3 * X * l * R :=
      hFull.trans (add_le_add hMain hRem)
    _ = 5 * (X * l) * R := by ring
    _ <= 5 * (Y * l) * R :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXY hl) (by norm_num)) hR

/-- Sum the complete multiplicity-counted zero contribution, with a uniform power. -/
theorem norm_tsum_robinZeroKernel_two_le_of_re_le
    {alpha : Real} (hAlpha : alpha <= 1)
    (hRoots : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= alpha)
    {x : Real} (hx : 1 < x) (hLog : 1 <= Real.log x) :
    norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
      robinZeroKernel 2 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p)) <=
      5 * (x ^ (alpha - 2) * Inv.inv (Real.log x)) *
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) := by
  let D : Real := 5 * (x ^ (alpha - 2) * Inv.inv (Real.log x))
  let W : RiemannXiDivisorZeroIndex -> Real := fun p =>
    (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)
  let F : RiemannXiDivisorZeroIndex -> Complex := fun p =>
    robinZeroKernel 2 (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p
  have hBound : forall p, norm (F p) <= D * W p := by
    intro p
    exact norm_robinZeroKernel_two_le_of_re_le hAlpha (hRoots p)
      (riemannXiDivisorZeroValue_ne_zero p) hx hLog
  have hSum : Summable (fun p => D * W p) :=
    summable_riemannXiDivisorZero_norm_inv_sq.mul_left D
  have hAbs : Summable (fun p => norm (F p)) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg (F p)) hBound hSum
  calc
    _ <= tsum (fun p => norm (F p)) := norm_tsum_le_tsum_norm hAbs
    _ <= tsum (fun p => D * W p) := hAbs.tsum_le_tsum hBound hSum
    _ = _ := by rw [tsum_mul_left]

end Robin1984
