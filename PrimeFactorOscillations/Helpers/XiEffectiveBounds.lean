/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.XiVerticalLogDerivative

/-!
# Explicit constants for xi height and horizontal variation

The only analytic values in these constants are fixed real zeta logarithmic
 derivatives and explicit convergent square tails. No residue-neighborhood
constant or existential uniform Euler bound is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Complex Robin1984

def xiEulerBound (a : Real) : Real := norm (zetaEulerLogDeriv (a : Complex))

def xiEulerLipschitz (a : Real) : Real :=
  2 * xiEulerBound (1 + (a - 1) / 2) / ((a - 1) / 2)

def xiExplicitHeight (a b : Real) : Real :=
  1 / (a - 1) + xiEulerBound a + abs (Real.log Real.pi) / 2 +
    (abs b + 8 + abs (Real.log 3) + abs Real.eulerMascheroniConstant) / 2

def xiExplicitLipschitz (a : Real) : Real :=
  xiEulerLipschitz a + 1 / (a - 1) ^ 2 +
    (tsum (fun n : Nat => 1 / (((n : Real) + 1) ^ 2))) / 4

theorem xiEulerBound_nonneg (a : Real) : 0 <= xiEulerBound a := norm_nonneg _

theorem zetaEulerLogDeriv_explicit_uniform (a : Real) (s : Complex)
    (ha : 1 < a) (hs : a <= s.re) : norm (zetaEulerLogDeriv s) <= xiEulerBound a := by
  have hh := dlog_riemannZeta_bdd_on_vertical_lines_generalized a s.re s.im ha hs
  rw [Complex.re_add_im] at hh
  simpa only [zetaEulerLogDeriv, xiEulerBound, neg_div, norm_neg] using hh

theorem zetaEulerLogDeriv_explicit_lipschitz (a : Real) (ha : 1 < a) :
    forall s z : Complex, a <= s.re -> a <= z.re ->
      norm (zetaEulerLogDeriv z - zetaEulerLogDeriv s) <=
        xiEulerLipschitz a * norm (z - s) := by
  let d : Real := (a - 1) / 2
  let M : Real := xiEulerBound (1 + d)
  have hd : 0 < d := by dsimp only [d]; linarith only [ha]
  have hM : 0 <= M := norm_nonneg _
  have hUniform (z : Complex) (hz : 1 + d <= z.re) :
      norm (zetaEulerLogDeriv z) <= M := by
    exact zetaEulerLogDeriv_explicit_uniform (1 + d) z
      (by linarith only [hd]) hz
  have hDeriv (z : Complex) (hz : a <= z.re) :
      norm (deriv zetaEulerLogDeriv z) <= 2 * M / d := by
    have hCenter : 1 + d <= z.re := by
      dsimp only [d]
      linarith only [ha, hz]
    have hLower (w : Complex) (hw : Membership.mem (Metric.ball z d) w) :
        1 + d <= w.re := by
      have hDistance : norm (z - w) < d := by
        rw [norm_sub_rev]
        simpa only [dist_eq_norm] using Metric.mem_ball.mp hw
      have hh := Complex.re_le_norm (z - w)
      simp only [Complex.sub_re] at hh
      dsimp only [d] at *
      linarith only [hz, hh, hDistance]
    have hDiff : DifferentiableOn Complex zetaEulerLogDeriv (Metric.ball z d) := by
      intro w hw
      exact (zetaEulerLogDeriv_differentiable
        (show 1 < w.re by linarith only [hLower w hw, hd])).differentiableWithinAt
    have hMaps : Set.MapsTo zetaEulerLogDeriv (Metric.ball z d)
        (Metric.closedBall (zetaEulerLogDeriv z) (2 * M)) := by
      intro w hw
      change dist (zetaEulerLogDeriv w) (zetaEulerLogDeriv z) <= 2 * M
      rw [dist_eq_norm]
      have hh := norm_sub_le (zetaEulerLogDeriv w) (zetaEulerLogDeriv z)
      have hW := hUniform w (hLower w hw)
      have hZ := hUniform z hCenter
      linarith only [hh, hW, hZ]
    exact Complex.norm_deriv_le_div_of_mapsTo_ball hDiff hMaps hd
  have hConvex : Convex Real {z : Complex | a <= z.re} := by
    intro x hx y hy c e hc he hce
    change a <= Complex.reCLM (HSMul.hSMul c x + HSMul.hSMul e y)
    rw [map_add, map_smul, map_smul]
    change a <= c * x.re + e * y.re
    calc
      a = (c + e) * a := by rw [hce, one_mul]
      _ = c * a + e * a := by ring
      _ <= _ := _root_.add_le_add
        (mul_le_mul_of_nonneg_left hx hc) (mul_le_mul_of_nonneg_left hy he)
  intro s z hs hz
  change norm (zetaEulerLogDeriv z - zetaEulerLogDeriv s) <=
    (2 * M / d) * norm (z - s)
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w hw => zetaEulerLogDeriv_differentiable (ha.trans_le hw))
    hDeriv hConvex hs hz

theorem xi_logDeriv_explicit_height (a b : Real) (ha : 1 < a) :
    forall s : Complex, a <= s.re -> s.re <= b -> 2 <= abs s.im ->
      (logDeriv riemannXi s).re <=
        (1 / 2 : Real) * Real.log (abs s.im) + xiExplicitHeight a b := by
  let G : Real := abs b + 8 + abs (Real.log 3) + abs Real.eulerMascheroniConstant
  let C : Real := 1 / (a - 1) + xiEulerBound a + abs (Real.log Real.pi) / 2 + G / 2
  have ha0 : 0 < a - 1 := by linarith only [ha]
  have hG : 0 <= G := by dsimp only [G]; positivity
  intro s hsa hsb ht
  change (logDeriv riemannXi s).re <= (1 / 2 : Real) * Real.log (abs s.im) + C
  have hs1 : 1 < s.re := ha.trans_le hsa
  have hReciprocal : 1 / (s.re - 1) <= 1 / (a - 1) :=
    one_div_le_one_div_of_le ha0 (by linarith only [hsa])
  have hER : (zetaEulerLogDeriv s).re <= xiEulerBound a :=
    (Complex.re_le_norm _).trans (zetaEulerLogDeriv_explicit_uniform a s ha hsa)
  have hPole : (1 / (s - 1)).re <= 1 / (a - 1) := by
    apply (Complex.re_le_norm _).trans
    rw [one_div, norm_inv, <- one_div]
    apply one_div_le_one_div_of_le ha0
    have h := Complex.re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith only [h, hsa]
  have h2 : (2 : Complex) = ((2 : Real) : Complex) := by norm_num
  have hGR : (s / 2 + 1).re = s.re / 2 + 1 := by
    rw [Complex.add_re, Complex.one_re, h2, Complex.div_ofReal_re]
  have hGI : (s / 2 + 1).im = s.im / 2 := by
    rw [Complex.add_im, Complex.one_im, h2, Complex.div_ofReal_im, add_zero]
  have hGt : 1 <= abs (s / 2 + 1).im := by
    rw [hGI, abs_div]
    norm_num
    linarith only [ht]
  have hPsi := digamma_re_height_upper (s / 2 + 1) (abs b + 2)
    (by rw [hGR]; linarith only [hs1])
    (by
      rw [hGR]
      have hb := le_abs_self b
      have hb0 := abs_nonneg b
      linarith only [hsb, hb, hb0]) hGt
  have hIm : abs (s / 2 + 1).im <= abs s.im := by
    rw [hGI, abs_div]
    norm_num
  have hLog : Real.log (abs (s / 2 + 1).im) <= Real.log (abs s.im) :=
    Real.log_le_log (by linarith only [hGt]) hIm
  have hPsiFinal : (digamma (s / 2 + 1)).re <= Real.log (abs s.im) + G := by
    have hh := le_abs_self (Real.log 3)
    dsimp only [G]
    linarith only [hPsi, hLog, hh]
  have hF : (logDeriv riemannXi s).re =
      (zetaEulerLogDeriv s).re + (1 / (s - 1)).re -
        (1 / 2 : Real) * Real.log Real.pi +
        (1 / 2 : Real) * (digamma (s / 2 + 1)).re := by
    rw [xi_logDeriv_euler_gamma hs1]
    simp
  have hPi := neg_le_abs (Real.log Real.pi)
  dsimp only [C]
  linarith only [hF, hER, hPole, hPsiFinal, hPi]

theorem xi_logDeriv_explicit_lipschitz (a : Real) (ha : 1 < a) :
    forall s z : Complex, a <= s.re -> a <= z.re ->
      norm (logDeriv riemannXi z - logDeriv riemannXi s) <=
        xiExplicitLipschitz a * norm (z - s) := by
  let L : Real := xiEulerLipschitz a
  have hL : 0 <= L := by
    dsimp only [L, xiEulerLipschitz]
    exact div_nonneg (mul_nonneg (by norm_num) (xiEulerBound_nonneg _))
      (by linarith only [ha])
  have hEuler := zetaEulerLogDeriv_explicit_lipschitz a ha
  let d : Real := a - 1
  let W : Real := tsum (fun n : Nat => 1 / (((n : Real) + 1) ^ 2))
  let C : Real := L + 1 / d ^ 2 + W / 4
  have hd : 0 < d := by dsimp only [d]; linarith only [ha]
  have hW : 0 <= W := tsum_nonneg (fun n => by positivity)
  intro s z hs hz
  change norm (logDeriv riemannXi z - logDeriv riemannXi s) <= C * norm (z - s)
  have hs1 : 1 < s.re := ha.trans_le hs
  have hz1 : 1 < z.re := ha.trans_le hz
  have hDs : d <= norm (s - 1) := by
    have hh := Complex.re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re] at hh
    dsimp only [d]
    linarith only [hh, hs]
  have hDz : d <= norm (z - 1) := by
    have hh := Complex.re_le_norm (z - 1)
    simp only [Complex.sub_re, Complex.one_re] at hh
    dsimp only [d]
    linarith only [hh, hz]
  have hs0 : Not (s - 1 = 0) := norm_pos_iff.mp (hd.trans_le hDs)
  have hz0 : Not (z - 1 = 0) := norm_pos_iff.mp (hd.trans_le hDz)
  have hPoleIdentity : 1 / (z - 1) - 1 / (s - 1) =
      (s - z) / ((z - 1) * (s - 1)) := by
    field_simp [hs0, hz0]
    ring
  have hPole : norm (1 / (z - 1) - 1 / (s - 1)) <= norm (z - s) / d ^ 2 := by
    rw [hPoleIdentity, norm_div, norm_mul, norm_sub_rev s z]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hd)
    have hh := mul_le_mul hDz hDs hd.le (norm_nonneg _)
    nlinarith only [hh]
  have h2 : (2 : Complex) = ((2 : Real) : Complex) := by norm_num
  have hGR (v : Complex) : (v / 2 + 1).re = v.re / 2 + 1 := by
    rw [Complex.add_re, Complex.one_re, h2, Complex.div_ofReal_re]
  have hGamma := digamma_lipschitz_right (z / 2 + 1) (s / 2 + 1)
    (by rw [hGR]; linarith only [hz1])
    (by rw [hGR]; linarith only [hs1])
  have hGammaIdentity : (z / 2 + 1) - (s / 2 + 1) = (z - s) / 2 := by ring
  have hGammaBound : norm (digamma (z / 2 + 1) - digamma (s / 2 + 1)) <=
      norm (z - s) / 2 * W := by
    change norm (digamma (z / 2 + 1) - digamma (s / 2 + 1)) <=
      norm ((z / 2 + 1) - (s / 2 + 1)) * W at hGamma
    rw [hGammaIdentity, norm_div] at hGamma
    norm_num at hGamma
    exact hGamma
  have hIdentity : logDeriv riemannXi z - logDeriv riemannXi s =
      (zetaEulerLogDeriv z - zetaEulerLogDeriv s) +
      (1 / (z - 1) - 1 / (s - 1)) +
      (1 / 2 : Complex) * (digamma (z / 2 + 1) - digamma (s / 2 + 1)) := by
    rw [xi_logDeriv_euler_gamma hz1, xi_logDeriv_euler_gamma hs1]
    ring
  have hTriangle : norm (logDeriv riemannXi z - logDeriv riemannXi s) <=
      norm (zetaEulerLogDeriv z - zetaEulerLogDeriv s) +
      norm (1 / (z - 1) - 1 / (s - 1)) +
      (1 / 2 : Real) * norm (digamma (z / 2 + 1) - digamma (s / 2 + 1)) := by
    rw [hIdentity]
    have h0 := norm_add_le (zetaEulerLogDeriv z - zetaEulerLogDeriv s)
      (1 / (z - 1) - 1 / (s - 1))
    have h1 := norm_add_le
      ((zetaEulerLogDeriv z - zetaEulerLogDeriv s) +
        (1 / (z - 1) - 1 / (s - 1)))
      ((1 / 2 : Complex) * (digamma (z / 2 + 1) - digamma (s / 2 + 1)))
    rw [norm_mul] at h1
    norm_num at h1
    simp only [one_div] at h0 h1
    simp only [one_div]
    linarith only [h0, h1]
  calc
    norm (logDeriv riemannXi z - logDeriv riemannXi s) <=
        norm (zetaEulerLogDeriv z - zetaEulerLogDeriv s) +
        norm (1 / (z - 1) - 1 / (s - 1)) +
        (1 / 2 : Real) * norm (digamma (z / 2 + 1) - digamma (s / 2 + 1)) := hTriangle
    _ <= L * norm (z - s) + norm (z - s) / d ^ 2 +
        (1 / 2 : Real) * (norm (z - s) / 2 * W) := by
      exact _root_.add_le_add (_root_.add_le_add (hEuler s z hs hz) hPole)
        (mul_le_mul_of_nonneg_left hGammaBound (by norm_num))
    _ = C * norm (z - s) := by dsimp only [C]; ring

theorem xiExplicitHeight_ge_pole (a b : Real) :
    1 / (a - 1) <= xiExplicitHeight a b := by
  have hB := xiEulerBound_nonneg a
  have hPi := abs_nonneg (Real.log Real.pi)
  have hb := abs_nonneg b
  have h3 := abs_nonneg (Real.log 3)
  have hg := abs_nonneg Real.eulerMascheroniConstant
  dsimp only [xiExplicitHeight]
  linarith only [hB, hPi, hb, h3, hg]

theorem xiExplicitHeight_nonneg (a b : Real) (ha : 1 < a) :
    0 <= xiExplicitHeight a b := by
  have hh := xiExplicitHeight_ge_pole a b
  exact (div_nonneg (by norm_num) (by linarith only [ha])).trans hh

theorem xiExplicitLipschitz_nonneg (a : Real) (ha : 1 < a) :
    0 <= xiExplicitLipschitz a := by
  have hW : 0 <= tsum (fun n : Nat => 1 / (((n : Real) + 1) ^ 2)) :=
    tsum_nonneg (fun n => by positivity)
  have hE : 0 <= xiEulerLipschitz a := by
    dsimp only [xiEulerLipschitz]
    exact div_nonneg (mul_nonneg (by norm_num) (xiEulerBound_nonneg _))
      (by linarith only [ha])
  dsimp only [xiExplicitLipschitz]
  positivity

end PrimeFactorOscillations
