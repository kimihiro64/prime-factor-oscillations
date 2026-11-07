/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.Complex.RealResiduePacket

/-!
# Reference multiplicity from a single residue phase

The imaginary part of an affine residue code eliminates its target order
exactly. The positive zero-product kernel also converts a strip and a height
bound into a finite multiplicity budget.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

def residuePhaseCoefficient (d : Real) (z : Complex) : Real :=
  d * (d - 1) * z.im / normSq (z + (d : Complex) - 1)

def residueReferencePhase (d : Real) (z r : Complex) : Real :=
  normSq (z + (d : Complex) - 1) * r.im / (d * (d - 1) * z.im)

theorem realPowerResidueCode_im (d : Real) (z : Complex) (a b : Int) :
    (realPowerResidueCode d z a b).im =
      residuePhaseCoefficient d z * (b : Real) := by
  unfold realPowerResidueCode residuePhaseCoefficient
  simp only [Complex.add_im, Complex.neg_im, Complex.intCast_im,
    Complex.mul_im, Complex.mul_re, Complex.div_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
    Complex.add_re, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

theorem residuePhaseCoefficient_pos (d : Real) (z : Complex)
    (hd : 1 < d) (hz : 0 < z.im) :
    0 < residuePhaseCoefficient d z := by
  have hden : Not (z + (d : Complex) - 1 = 0) := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im,
      Complex.one_im, Complex.zero_im, add_zero, sub_zero] at hi
    linarith
  unfold residuePhaseCoefficient
  exact div_pos (mul_pos (mul_pos (by linarith) (by linarith)) hz)
    (Complex.normSq_pos.mpr hden)

theorem residueReferencePhase_code (d : Real) (z : Complex) (a b : Int)
    (hd : 1 < d) (hz : Not (z.im = 0)) :
    residueReferencePhase d z (realPowerResidueCode d z a b) = (b : Real) := by
  have hden : Not (z + (d : Complex) - 1 = 0) := by
    intro h
    apply hz
    simpa using congrArg Complex.im h
  have hn : Not (normSq (z + (d : Complex) - 1) = 0) :=
    ne_of_gt (Complex.normSq_pos.mpr hden)
  have hd0 : Not (d = 0) := ne_of_gt (by linarith : 0 < d)
  have hd1 : Not (d - 1 = 0) := ne_of_gt (by linarith : 0 < d - 1)
  unfold residueReferencePhase
  rw [realPowerResidueCode_im]
  unfold residuePhaseCoefficient
  field_simp [hn, hd0, hd1, hz]

def criticalPhaseAnchor (d t : Real) : Complex := Complex.mk (1 / 2) (d * t)

def criticalPhaseReference (d t : Real) : Complex :=
  Complex.mk (1 - 1 / (2 * d)) t

def criticalPhaseDegree (b : Real) : Real := 1 / (2 * (1 - b))

theorem criticalPhaseDegree_mul (b : Real) (hb : b < 1) :
    criticalPhaseDegree b * (2 * (1 - b)) = 1 := by
  have hb0 : Not (1 - b = 0) := ne_of_gt (sub_pos.mpr hb)
  unfold criticalPhaseDegree
  field_simp [hb0]

theorem criticalPhaseDegree_gt_one (b : Real)
    (hb : 1 / 2 < b) (hb1 : b < 1) :
    1 < criticalPhaseDegree b := by
  have h := criticalPhaseDegree_mul b hb1
  have hd : 0 < criticalPhaseDegree b := by
    unfold criticalPhaseDegree
    exact div_pos (by norm_num) (by linarith)
  nlinarith

theorem criticalPhaseReference_degree (b t : Real) (hb : b < 1) :
    criticalPhaseReference (criticalPhaseDegree b) t = Complex.mk b t := by
  have h := criticalPhaseDegree_mul b hb
  have hd : Not (criticalPhaseDegree b = 0) := by
    intro hz
    rw [hz, zero_mul] at h
    norm_num at h
  apply Complex.ext
  . change 1 - 1 / (2 * criticalPhaseDegree b) = b
    apply (eq_sub_iff_add_eq).mp
    have he : 1 / (2 * criticalPhaseDegree b) = 1 - b := by
      apply (div_eq_iff (mul_ne_zero (by norm_num) hd)).mpr
      nlinarith [h]
    rw [he]
    ring
  . rfl

/-- A product-kernel lower bound, retaining the complete horizontal term. -/
theorem inverse_product_strip_lower (z : Complex) (s : Real)
    (hLo : 0 < z.re) (hHi : z.re < 1)
    (hs : s <= z.re * (1 - z.re)) :
    1 <= (z.im ^ 2 + 1 - 3 * s) *
      ((z * (1 - z)) ^ (-1 : Int)).re := by
  let c : Real := z.re * (1 - z.re)
  let u : Real := z.im ^ 2
  let v : Real := normSq (z * (1 - z))
  have hc : 0 < c := mul_pos hLo (by linarith)
  have hc1 : 4 * c <= 1 := by
    dsimp only [c]
    nlinarith [sq_nonneg (2 * z.re - 1)]
  have hu : 0 <= u := sq_nonneg _
  have hRe : (z * (1 - z)).re = u + c := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    dsimp only [u, c]
    ring
  have hn : Not (z * (1 - z) = 0) := by
    intro h
    have hh := congrArg Complex.re h
    rw [hRe] at hh
    change u + c = 0 at hh
    linarith
  have hv : 0 < v := Complex.normSq_pos.mpr hn
  have hPoly : v = u ^ 2 + (1 - 2 * c) * u + c ^ 2 := by
    dsimp only [v, u, c]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hBound : v <= (u + 1 - 3 * s) * (u + c) := by
    have hp := mul_nonneg (sub_nonneg.mpr hs) (add_nonneg hu hc.le)
    have hq := mul_nonneg hc.le (sub_nonneg.mpr hc1)
    change 0 <= (c - s) * (u + c) at hp
    rw [hPoly]
    nlinarith only [hp, hq]
  have hk : ((z * (1 - z)) ^ (-1 : Int)).re = (u + c) / v := by
    rw [zpow_neg_one, Complex.inv_re, hRe]
  calc
    1 = v * Inv.inv v := by field_simp
    _ <= ((u + 1 - 3 * s) * (u + c)) * Inv.inv v :=
      mul_le_mul_of_nonneg_right hBound (inv_nonneg.mpr hv.le)
    _ = (z.im ^ 2 + 1 - 3 * s) *
        ((z * (1 - z)) ^ (-1 : Int)).re := by
      rw [hk]
      change _ = (u + 1 - 3 * s) * ((u + c) / v)
      ring

theorem inverse_product_seven_eighths_lower (z : Complex)
    (hLo : (1 / 8 : Real) <= z.re) (hHi : z.re <= (7 / 8 : Real)) :
    1 <= (z.im ^ 2 + 43 / 64) *
      ((z * (1 - z)) ^ (-1 : Int)).re := by
  have hs : (7 / 64 : Real) <= z.re * (1 - z.re) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hLo) (sub_nonneg.mpr hHi)]
  have h := inverse_product_strip_lower z (7 / 64) (by linarith) (by linarith) hs
  convert h using 1; ring

end Complex
