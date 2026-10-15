/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.LPFMajorZeroStrip

/-!
# Numerical logarithmic-derivative bounds on the fixed major-arc disk

The Schwarz transform retains the real-part cancellation in a normalized
analytic logarithm. On the radius 9/8 disk, a real-part bound B yields
a derivative bound 3328 B throughout the radius 17/16 inner disk.
Application to the actual Dirichlet L-function still requires construction
and growth bounds for that normalized analytic logarithm.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

theorem lpf_log_disc_norm_bound (g : Complex -> Complex) (c z : Complex)
    (B r : Real) (hB : 0 < B) (hr0 : 0 <= r) (hr : r < 9 / 8)
    (hg : DifferentiableOn Complex g (Metric.ball c (9 / 8 : Real)))
    (hgc : g c = 0)
    (hRe : forall w : Complex, Membership.mem (Metric.ball c (9 / 8 : Real)) w ->
      (g w).re <= B)
    (hz : dist z c <= r) :
    norm (g z) <= 2 * B * r / (9 / 8 - r) := by
  let h : Complex -> Complex := fun w => g w / (((2 * B : Real) : Complex) - g w)
  have hDen (w : Complex) (hw : Membership.mem (Metric.ball c (9 / 8 : Real)) w) :
      Not ((((2 * B : Real) : Complex) - g w) = 0) := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hh
    have hR := hRe w hw
    linarith only [hh, hR, hB]
  have hNorm (w : Complex) (hw : Membership.mem (Metric.ball c (9 / 8 : Real)) w) :
      norm (g w) <= norm (((2 * B : Real) : Complex) - g w) := by
    have hR := hRe w hw
    have hSq : norm (g w) ^ 2 <= norm (((2 * B : Real) : Complex) - g w) ^ 2 := by
      rw [<- Complex.normSq_eq_norm_sq, <- Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im]
      nlinarith only [mul_nonneg hB.le (sub_nonneg.mpr hR)]
    nlinarith only [hSq, norm_nonneg (g w), norm_nonneg (((2 * B : Real) : Complex) - g w)]
  have hh : DifferentiableOn Complex h (Metric.ball c (9 / 8 : Real)) :=
    hg.div ((differentiableOn_const (((2 * B : Real) : Complex))).sub hg) hDen
  have hc : h c = 0 := by simp only [h, hgc, zero_div]
  have hMaps : Set.MapsTo h (Metric.ball c (9 / 8 : Real)) (Metric.closedBall (h c) 1) := by
    intro w hw
    have hPos : 0 < norm (((2 * B : Real) : Complex) - g w) := norm_pos_iff.mpr (hDen w hw)
    have hBound := div_le_div_of_nonneg_right (hNorm w hw) hPos.le
    rw [div_self hPos.ne'] at hBound
    change dist (h w) (h c) <= 1
    rw [hc, dist_zero_right]
    exact (by simpa only [h, norm_div] using hBound)
  have hzBall : Membership.mem (Metric.ball c (9 / 8 : Real)) z :=
    Metric.mem_ball.mpr (hz.trans_lt hr)
  have hSchwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball hh hMaps hzBall
  rw [hc, dist_zero_right] at hSchwarz
  have hSmall : norm (h z) <= r / (9 / 8 : Real) := by
    have hd := div_le_div_of_nonneg_right hz (by norm_num : (0 : Real) <= 9 / 8)
    have he : (1 : Real) / (9 / 8) * dist z c = dist z c / (9 / 8) := by ring
    rw [he] at hSchwarz
    exact hSchwarz.trans hd
  have hTriangle : norm (((2 * B : Real) : Complex) - g z) <= 2 * B + norm (g z) := by
    have h := norm_sub_le (((2 * B : Real) : Complex)) (g z)
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * B)] using h
  have hIdentity : norm (g z) = norm (h z) * norm (((2 * B : Real) : Complex) - g z) := by
    dsimp [h]
    rw [norm_div]
    have hNe := (norm_pos_iff.mpr (hDen z hzBall)).ne'
    have hCancel : (norm (g z) * norm (((2 * B : Real) : Complex) - g z)) /
        norm (((2 * B : Real) : Complex) - g z) = norm (g z) :=
      (div_eq_iff hNe).mpr rfl
    calc
      _ = (norm (g z) * norm (((2 * B : Real) : Complex) - g z)) /
          norm (((2 * B : Real) : Complex) - g z) := hCancel.symm
      _ = _ := by ring
  have hBound : norm (g z) <= (r / (9 / 8 : Real)) * (2 * B + norm (g z)) := by
    calc
      _ = norm (h z) * norm (((2 * B : Real) : Complex) - g z) := hIdentity
      _ <= _ := mul_le_mul hSmall hTriangle (norm_nonneg _) (div_nonneg hr0 (by norm_num))
  have hCross : norm (g z) * (9 / 8 - r) <= 2 * B * r := by
    norm_num [div_eq_mul_inv] at hBound
    nlinarith only [hBound]
  apply (mul_le_mul_iff_of_pos_right (by linarith only [hr] : 0 < (9 / 8 : Real) - r)).mp
  have hCancel : (2 * B * r / (9 / 8 - r)) * (9 / 8 - r) = 2 * B * r := by
    have hNe : Not ((9 / 8 : Real) - r = 0) := by linarith only [hr]
    have hCancel : (2 * B * r * (9 / 8 - r)) / (9 / 8 - r) = 2 * B * r :=
      (div_eq_iff hNe).mpr rfl
    calc
      _ = (2 * B * r * (9 / 8 - r)) / (9 / 8 - r) := by ring
      _ = _ := hCancel
  rw [hCancel]
  exact hCross

theorem lpf_log_disc_deriv_bound (g : Complex -> Complex) (c z : Complex)
    (B : Real) (hB : 0 < B)
    (hg : DifferentiableOn Complex g (Metric.ball c (9 / 8 : Real)))
    (hgc : g c = 0)
    (hRe : forall w : Complex, Membership.mem (Metric.ball c (9 / 8 : Real)) w ->
      (g w).re <= B)
    (hz : dist z c <= 17 / 16) :
    norm (deriv g z) <= 3328 * B := by
  have hCenter : norm (g z) <= 34 * B := by
    have h := lpf_log_disc_norm_bound g c z B (17 / 16) hB
      (by norm_num) (by norm_num) hg hgc hRe hz
    convert h using 1 <;> ring
  have hDist (w : Complex) (hw : Membership.mem (Metric.ball z (1 / 32 : Real)) w) :
      dist w c <= 35 / 32 := by
    have h := dist_triangle w z c
    have hh := Metric.mem_ball.mp hw
    linarith only [h, hh, hz]
  have hSub : Metric.ball z (1 / 32 : Real) <= Metric.ball c (9 / 8 : Real) := by
    intro w hw
    exact Metric.mem_ball.mpr ((hDist w hw).trans_lt (by norm_num))
  have hMaps : Set.MapsTo g (Metric.ball z (1 / 32 : Real))
      (Metric.closedBall (g z) (104 * B)) := by
    intro w hw
    have hW : norm (g w) <= 70 * B := by
      have h := lpf_log_disc_norm_bound g c w B (35 / 32) hB
        (by norm_num) (by norm_num) hg hgc hRe (hDist w hw)
      convert h using 1 <;> ring
    have hNorm := norm_sub_le (g w) (g z)
    change dist (g w) (g z) <= 104 * B
    rw [dist_eq_norm]
    linarith only [hNorm, hW, hCenter]
  have h := Complex.norm_deriv_le_div_of_mapsTo_ball
    (hg.mono hSub) hMaps (by norm_num : (0 : Real) < 1 / 32)
  convert h using 1 <;> ring

end PrimeFactorOscillations.QRH
