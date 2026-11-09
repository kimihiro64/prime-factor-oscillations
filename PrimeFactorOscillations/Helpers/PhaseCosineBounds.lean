/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Certified phase evaluation for the signed finite Euler window

Only approximation and interval variation are bounded in norm.
The signed weighted phase values remain in the numerical main packet.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def phaseCosPolynomial (x : Real) : Real :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 -
    x ^ 10 / 3628800 + x ^ 12 / 479001600 - x ^ 14 / 87178291200

theorem phaseCosPolynomial_eq_real_sum (x : Real) :
    (Finset.sum (Finset.range 16) (fun k : Nat =>
      (((x : Complex) * Complex.I) ^ k) / (k.factorial : Complex))).re =
      phaseCosPolynomial x := by
  norm_num [Finset.sum_range_succ, pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply, phaseCosPolynomial] <;> ring

theorem phase_cos_poly_error (x : Real) (hx : abs x <= 4) :
    abs (Real.cos x - phaseCosPolynomial x) <= 1 / 2000 := by
  let z : Complex := (x : Complex) * Complex.I
  have hnorm : norm z <= 4 := by
    simpa only [z, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] using hx
  have hhalf : norm z / (17 : Real) <= 1 / 2 := by linarith only [hnorm]
  have hb := Complex.exp_bound' (x := z) (n := 16) hhalf
  have hpower : norm z ^ 16 <= (4 : Real) ^ 16 := by gcongr
  have hsmall : norm (Complex.exp z - Finset.sum (Finset.range 16)
      (fun k : Nat => z ^ k / (k.factorial : Complex))) <= 1 / 2000 := by
    norm_num at hb
    linarith only [hb, hpower]
  have hr := (Complex.abs_re_le_norm
    (Complex.exp z - Finset.sum (Finset.range 16)
      (fun k : Nat => z ^ k / (k.factorial : Complex)))).trans hsmall
  simpa only [Complex.sub_re, z, Complex.exp_ofReal_mul_I_re,
    phaseCosPolynomial_eq_real_sum] using hr

theorem phase_cos_shift_error (theta q c d e : Real) (k : Int)
    (hq : abs q <= 4) (hPoly : abs (phaseCosPolynomial q - c) <= e)
    (hPhase : abs (theta - (k : Real) * (2 * Real.pi) - q) <= d) :
    abs (Real.cos theta - c) <= d + 1 / 2000 + e := by
  have hPeriod : Real.cos theta = Real.cos (theta - (k : Real) * (2 * Real.pi)) := by
    calc
      Real.cos theta = Real.cos
          ((theta - (k : Real) * (2 * Real.pi)) + (k : Real) * (2 * Real.pi)) := by
        congr 1
        ring
      _ = Real.cos (theta - (k : Real) * (2 * Real.pi)) :=
        Real.cos_add_int_mul_two_pi _ k
  have h0 := Real.abs_cos_sub_cos_le (theta - (k : Real) * (2 * Real.pi)) q
  have h1 := phase_cos_poly_error q hq
  have h2 := _root_.abs_sub_le (Real.cos q) (phaseCosPolynomial q) c
  have h3 := _root_.abs_sub_le
    (Real.cos (theta - (k : Real) * (2 * Real.pi))) (Real.cos q) c
  rw [hPeriod]
  linarith only [h0, hPhase, h1, hPoly, h2, h3]

theorem phase_weighted_upper (theta w lo hi c : Real)
    (hLo : lo <= w) (hHi : w <= hi) (hw : 0 <= w) (hCos : c <= Real.cos theta) :
    -w * Real.cos theta <= max (-lo * c) (-hi * c) := by
  have hMain := mul_nonneg hw (sub_nonneg.mpr hCos)
  by_cases hc : 0 <= c
  next =>
    have hWeight := mul_nonneg (sub_nonneg.mpr hLo) hc
    have hMax := le_max_left (-lo * c) (-hi * c)
    nlinarith only [hMain, hWeight, hMax]
  next =>
    have hWeight := mul_nonneg (sub_nonneg.mpr hHi) (neg_nonneg.mpr (le_of_not_ge hc))
    have hMax := le_max_right (-lo * c) (-hi * c)
    nlinarith only [hMain, hWeight, hMax]

end PrimeFactorOscillations
