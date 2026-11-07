/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Real.Pi.Bounds
import PrimeFactorOscillations.Helpers.EulerRealHalfIntegerBounds
import PrimeFactorOscillations.Helpers.RealDigammaRemainder

/-!
# Signed constants for the two-line xi multiplicity estimate

The gamma logarithms, inverse endpoint correction and pole compensation
remain coupled at one common height.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Complex Robin1984

def compensatedGammaLog (q : Real) : Real :=
  Real.log (1 + (81 / 4) * q) - (2 / 3) * Real.log (1 + (121 / 4) * q)

def compensatedPoleSquared (y : Real) : Real :=
  (3 / 2) / ((3 / 2) ^ 2 + y) - (2 / 3) * (5 / 2) / ((5 / 2) ^ 2 + y)

def compensatedInverseSquared (y : Real) : Real :=
  (9 / 4) / ((9 / 4) ^ 2 + y / 4) - (2 / 3) * (11 / 4) / ((11 / 4) ^ 2 + y / 4)

theorem compensated_div_compare {a b c d : Real} (hb : 0 < b) (hd : 0 < d)
    (h : a * d <= c * b) : a / b <= c / d := by
  have he : (c / d - a / b) * (b * d) = c * b - a * d := by
    field_simp [hb.ne', hd.ne']
  have hn : 0 <= (c / d - a / b) * (b * d) := by rw [he]; linarith only [h]
  by_contra hh
  have hh1 : c / d - a / b < 0 := sub_neg.mpr (lt_of_not_ge hh)
  have hh2 := mul_neg_of_neg_of_pos hh1 (mul_pos hb hd)
  linarith only [hn, hh2]

theorem compensated_div_upper {a b c : Real} (hb : 0 < b)
    (h : a <= c * b) : a / b <= c := by
  simpa only [div_one, mul_one] using
    (compensated_div_compare (a := a) (c := c) hb (by norm_num : (0 : Real) < 1)
      (by simpa only [mul_one] using h))

theorem simplicity_log_six_lt_two : Real.log 6 < 2 := by
  rw [show (6 : Real) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]

theorem simplicity_log_two_pi_gt : 9 / 5 < Real.log (2 * Real.pi) := by
  have hd : 3 / Real.pi <= 150 / 157 := by
    apply compensated_div_upper Real.pi_pos
    linarith only [Real.pi_gt_d2]
  have hh := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : Real) < 3) Real.pi_pos)
  rw [Real.log_div (by norm_num) Real.pi_ne_zero] at hh
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero]
  linarith only [hh, hd, Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem compensatedGammaLog_ratio (q : Real) (hq : 0 <= q) :
    3 * compensatedGammaLog q =
      Real.log ((1 + (81 / 4) * q) ^ 3 / (1 + (121 / 4) * q) ^ 2) := by
  have hA : 0 < 1 + (81 / 4 : Real) * q := by linarith only [hq]
  have hB : 0 < 1 + (121 / 4 : Real) * q := by linarith only [hq]
  rw [Real.log_div (pow_ne_zero 3 hA.ne') (pow_ne_zero 2 hB.ne'), Real.log_pow, Real.log_pow]
  dsimp only [compensatedGammaLog]
  norm_num
  ring

theorem compensatedGammaLog_low (q : Real) (hq : 0 <= q) (hQ : q <= 1 / 4) :
    compensatedGammaLog q <= 1 / 2 := by
  have hA : 0 < 1 + (81 / 4 : Real) * q := by linarith only [hq]
  have hB : 0 < 1 + (121 / 4 : Real) * q := by linarith only [hq]
  have h2 : q ^ 2 <= q / 4 := by
    nlinarith only [mul_nonneg hq (sub_nonneg.mpr hQ)]
  have h3 : q ^ 3 <= q ^ 2 / 4 := by
    nlinarith only [mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hQ)]
  have hr : (1 + (81 / 4 : Real) * q) ^ 3 / (1 + (121 / 4 : Real) * q) ^ 2 <= 49 / 16 := by
    apply compensated_div_upper (pow_pos hB 2)
    nlinarith only [hQ, h2, h3]
  have hl := Real.log_le_log (div_pos (pow_pos hA 3) (pow_pos hB 2)) hr
  have hs := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 7 / 4)
  have he : Real.log (49 / 16 : Real) = 2 * Real.log (7 / 4 : Real) := by
    rw [show (49 / 16 : Real) = (7 / 4) ^ (2 : Nat) by norm_num, Real.log_pow]
    norm_num
  rw [<- compensatedGammaLog_ratio q hq, he] at hl
  linarith only [hl, hs]

theorem compensatedGammaLog_high (q : Real) (hq : 0 <= q) (hQ : q <= 1 / 36) :
    (9 / 10) * compensatedGammaLog q <= 17043 / 449440 := by
  have hA : 0 < 1 + (81 / 4 : Real) * q := by linarith only [hq]
  have hB : 0 < 1 + (121 / 4 : Real) * q := by linarith only [hq]
  have hr : (1 + (81 / 4 : Real) * q) ^ 3 / (1 + (121 / 4 : Real) * q) ^ 2 <= 50625 / 44944 := by
    apply compensated_div_upper (pow_pos hB 2)
    have hh := mul_nonneg (sub_nonneg.mpr hQ)
      (show 0 <= 16963375104 + 44539310592 * (36 * q) + 23885084304 * (36 * q) ^ 2 from by positivity)
    nlinarith only [hh]
  have hl := Real.log_le_log (div_pos (pow_pos hA 3) (pow_pos hB 2)) hr
  have hs := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 50625 / 44944)
  rw [<- compensatedGammaLog_ratio q hq] at hl
  linarith only [hl, hs]

theorem compensatedPoleSquared_low (y : Real) (hy : 4 <= y) :
    (18 / 5) * compensatedPoleSquared y <= 7 / 25 := by
  have hA : 0 < (3 / 2 : Real) ^ 2 + y := by linarith only [hy]
  have hB : 0 < (5 / 2 : Real) ^ 2 + y := by linarith only [hy]
  dsimp only [compensatedPoleSquared]
  have he : (3 / 2 : Real) / ((3 / 2) ^ 2 + y) -
      (2 / 3) * (5 / 2) / ((5 / 2) ^ 2 + y) =
      (45 / 8 - y / 6) / (((3 / 2) ^ 2 + y) * ((5 / 2) ^ 2 + y)) := by
    field_simp [hA.ne', hB.ne']
    ring
  rw [he]
  have hh : (45 / 8 - y / 6) / (((3 / 2) ^ 2 + y) * ((5 / 2) ^ 2 + y)) <= 7 / 90 := by
    apply compensated_div_upper (mul_pos hA hB)
    nlinarith only [hy, sq_nonneg (y - 4)]
  linarith only [hh]

theorem compensatedPoleSquared_high (y : Real) (hy : 36 <= y) :
    compensatedPoleSquared y <= 0 := by
  have hA : 0 < (3 / 2 : Real) ^ 2 + y := by linarith only [hy]
  have hB : 0 < (5 / 2 : Real) ^ 2 + y := by linarith only [hy]
  dsimp only [compensatedPoleSquared]
  apply sub_nonpos.mpr
  apply compensated_div_compare hA hB
  nlinarith only [hy]

theorem compensatedInverseSquared_nonneg (y : Real) (hy : 0 <= y) :
    0 <= compensatedInverseSquared y := by
  have hA : 0 < (9 / 4 : Real) ^ 2 + y / 4 := by linarith only [hy]
  have hB : 0 < (11 / 4 : Real) ^ 2 + y / 4 := by linarith only [hy]
  dsimp only [compensatedInverseSquared]
  apply sub_nonneg.mpr
  apply compensated_div_compare hB hA
  nlinarith only [hy]

theorem compensated_log_norm_vertical (u t : Real) (ht : Not (t = 0)) :
    Real.log (norm (Complex.mk u (t / 2))) = Real.log (abs t) - Real.log 2 +
      (1 / 2) * Real.log (1 + (4 * u ^ 2) * (1 / t ^ 2)) := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have he : norm (Complex.mk u (t / 2)) ^ 2 =
      (t ^ 2 / 4) * (1 + (4 * u ^ 2) * (1 / t ^ 2)) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change u * u + t / 2 * (t / 2) = _
    field_simp [ht]
    ring
  have hP : 0 < 1 + (4 * u ^ 2) * (1 / t ^ 2) := by positivity
  have hlog := congrArg Real.log he
  rw [Real.log_pow, Real.log_mul (ne_of_gt (div_pos ht2 (by norm_num))) hP.ne',
    Real.log_div (pow_ne_zero 2 ht) (by norm_num), Real.log_pow] at hlog
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
    norm_num
  rw [h4] at hlog
  simp only [Real.log_abs, one_div]
  norm_num at hlog
  linarith only [hlog]

theorem compensated_digamma_real_upper (t : Real) (ht : Not (t = 0)) :
    (18 / 5) * ((1 / 2) *
      ((Complex.digamma (Complex.mk (9 / 4) (t / 2))).re -
        (2 / 3) * (Complex.digamma (Complex.mk (11 / 4) (t / 2))).re) -
          (1 / 6) * Real.log Real.pi) <=
      (3 / 5) * Real.log (abs t) - (3 / 5) * Real.log (2 * Real.pi) +
        (9 / 10) * compensatedGammaLog (1 / t ^ 2) -
        (9 / 10) * compensatedInverseSquared (t ^ 2) + 70 / 1089 := by
  let zu : Complex := Complex.mk (9 / 4) (t / 2)
  let zv : Complex := Complex.mk (11 / 4) (t / 2)
  have hu := (abs_le.mp (Complex.digamma_real_log_norm_remainder zu (by norm_num [zu]))).2
  have hv := (abs_le.mp (Complex.digamma_real_log_norm_remainder zv (by norm_num [zv]))).1
  have hlogu := compensated_log_norm_vertical (9 / 4) t ht
  have hlogv := compensated_log_norm_vertical (11 / 4) t ht
  have hinv : (1 / zu).re - (2 / 3) * (1 / zv).re = compensatedInverseSquared (t ^ 2) := by
    norm_num [zu, zv, one_div, Complex.inv_re, Complex.normSq_apply,
      compensatedInverseSquared, div_pow]
    have hm : t / 2 * (t / 2) = t ^ 2 / 4 := by ring
    rw [hm]
    ring
  have hpi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  norm_num only [zu, zv] at hu hv
  norm_num only at hlogu hlogv
  dsimp only [compensatedGammaLog]
  norm_num only
  change _ <= _ at hu
  dsimp only [zu, zv] at hinv
  nlinarith only [hu, hv, hlogu, hlogv, hinv, hpi]

def compensatedXiScalar (t : Real) : Real :=
  (3 / 5) * Real.log (abs t) + 27 / 25 - (3 / 5) * Real.log (2 * Real.pi) +
    70 / 1089 + (9 / 10) * compensatedGammaLog (1 / t ^ 2) +
      (18 / 5) * compensatedPoleSquared (t ^ 2) -
        (9 / 10) * compensatedInverseSquared (t ^ 2)

theorem compensatedXiScalar_low (t : Real) (ht : 2 <= abs t) :
    compensatedXiScalar t <= (3 / 5) * Real.log (abs t) + 4 / 5 := by
  have hy : 4 <= t ^ 2 := by nlinarith only [ht, sq_abs t, sq_nonneg (abs t - 2)]
  have hq : 0 <= 1 / t ^ 2 := div_nonneg (by norm_num) (sq_nonneg t)
  have hQ : 1 / t ^ 2 <= 1 / 4 := one_div_le_one_div_of_le (by norm_num) hy
  have hg := compensatedGammaLog_low _ hq hQ
  have hp := compensatedPoleSquared_low _ hy
  have hi := compensatedInverseSquared_nonneg _ (sq_nonneg t)
  have hpi := simplicity_log_two_pi_gt
  dsimp only [compensatedXiScalar]
  linarith only [hg, hp, hi, hpi]

theorem compensatedXiScalar_high (t : Real) (ht : 6 <= abs t) :
    compensatedXiScalar t <= (3 / 5) * Real.log (abs t) + 11 / 100 := by
  have hy : 36 <= t ^ 2 := by nlinarith only [ht, sq_abs t, sq_nonneg (abs t - 6)]
  have hq : 0 <= 1 / t ^ 2 := div_nonneg (by norm_num) (sq_nonneg t)
  have hQ : 1 / t ^ 2 <= 1 / 36 := one_div_le_one_div_of_le (by norm_num) hy
  have hg := compensatedGammaLog_high _ hq hQ
  have hp := compensatedPoleSquared_high _ hy
  have hi := compensatedInverseSquared_nonneg _ (sq_nonneg t)
  have hpi := simplicity_log_two_pi_gt
  dsimp only [compensatedXiScalar]
  linarith only [hg, hp, hi, hpi]

theorem xi_logDeriv_point_euler_gamma (r t : Real) (hr : 1 / 2 < r) :
    (logDeriv riemannXi (xiResolventPoint r t)).re =
      (zetaEulerLogDeriv (xiResolventPoint r t)).re +
        (r - 1 / 2) / ((r - 1 / 2) ^ 2 + t ^ 2) -
          (1 / 2) * Real.log Real.pi +
            (1 / 2) * (Complex.digamma (Complex.mk (r / 2 + 5 / 4) (t / 2))).re := by
  have hs : 1 < (xiResolventPoint r t).re := by
    norm_num [xiResolventPoint]
    linarith only [hr]
  have harg : xiResolventPoint r t / 2 + 1 = Complex.mk (r / 2 + 5 / 4) (t / 2) := by
    apply Complex.ext <;> norm_num [xiResolventPoint, Complex.div_re, Complex.div_im,
      Complex.normSq_apply] <;> ring
  have hm : xiResolventPoint r t - 1 = Complex.mk (r - 1 / 2) t := by
    apply Complex.ext <;> norm_num [xiResolventPoint] <;> ring
  have hp : (1 / (xiResolventPoint r t - 1)).re =
      (r - 1 / 2) / ((r - 1 / 2) ^ 2 + t ^ 2) := by
    rw [hm]
    simp only [one_div, Complex.inv_re, Complex.normSq_apply, pow_two]
  have hg := congrArg Complex.re (xi_logDeriv_euler_gamma hs)
  rw [harg] at hg
  have hc : (1 / 2 : Complex) = ((1 / 2 : Real) : Complex) := by norm_num
  rw [hc] at hg
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hg
  rw [hp] at hg
  exact hg

theorem xi_compensated_scalar_bound (t : Real) (ht : 2 <= abs t) :
    (18 / 5) * ((logDeriv riemannXi (xiResolventPoint 2 t)).re -
      (2 / 3) * (logDeriv riemannXi (xiResolventPoint 3 t)).re) <= compensatedXiScalar t := by
  have hs : 1 < (xiResolventPoint 2 t).re := by norm_num [xiResolventPoint]
  have he := zetaEulerLogDeriv_compensated_bound (xiResolventPoint 2 t) (2 / 3)
    hs (by norm_num) (by norm_num)
  have hs1 : xiResolventPoint 2 t + 1 = xiResolventPoint 3 t := by
    simp only [xiResolventPoint]
    push_cast
    ring
  rw [hs1] at he
  have hsr : (xiResolventPoint 2 t).re = 5 / 2 := by norm_num [xiResolventPoint]
  rw [hsr] at he
  have hr := (Complex.re_le_norm _).trans (he.trans xiEulerBound_five_halves)
  have hc : ((2 / 3 : Real) : Complex) = (2 / 3 : Complex) := by norm_num
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hr
  have ht0 : Not (t = 0) := by intro h; simp only [h, abs_zero] at ht; linarith only [ht]
  have hg := compensated_digamma_real_upper t ht0
  have hx2 := xi_logDeriv_point_euler_gamma 2 t (by norm_num)
  have hx3 := xi_logDeriv_point_euler_gamma 3 t (by norm_num)
  norm_num only at hx2 hx3
  dsimp only [compensatedXiScalar, compensatedPoleSquared]
  simp only [div_eq_mul_inv] at hr hg hx2 hx3
  simp only [div_eq_mul_inv]
  norm_num only at hr hg hx2 hx3
  norm_num only
  linarith only [hr, hg, hx2, hx3]

end PrimeFactorOscillations
