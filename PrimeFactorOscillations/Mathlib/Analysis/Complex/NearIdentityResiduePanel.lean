/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.Complex.RealResiduePacket

/-!
# Geometry for finite panels of compensation powers approaching one

The affine orbit is injective in its natural parameter. Its inverse real
part has a uniform positive floor on a fixed right-half-strip rectangle.
The original signed residue keeps its full nonnegative reference term.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Complex

def nearIdentityFraction (j : Nat) : Real :=
  ((j + 1 : Nat) : Real) / ((j + 2 : Nat) : Real)

def nearIdentityPoint (j : Nat) (z : Complex) : Complex :=
  (nearIdentityFraction j : Complex) * z + (1 - (nearIdentityFraction j : Complex))

theorem nearIdentityFraction_mul_den (j : Nat) :
    nearIdentityFraction j * (j + 2 : Nat) = (j + 1 : Nat) := by
  have hDen : Not (((j + 2 : Nat) : Real) = 0) := by positivity
  unfold nearIdentityFraction
  field_simp [hDen]

theorem nearIdentityFraction_bounds (j : Nat) :
    And (0 < nearIdentityFraction j) (nearIdentityFraction j < 1) := by
  have hDen : (0 : Real) < (j + 2 : Nat) := by positivity
  constructor
  . unfold nearIdentityFraction
    exact div_pos (by positivity) hDen
  . by_contra h
    have hProduct := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h)) hDen.le
    have hIdentity := nearIdentityFraction_mul_den j
    push_cast at hProduct hIdentity
    nlinarith only [hProduct, hIdentity]

theorem nearIdentityFraction_injective : Function.Injective nearIdentityFraction := by
  intro a b h
  have ha := nearIdentityFraction_mul_den a
  have hb := nearIdentityFraction_mul_den b
  rw [<- h] at hb
  push_cast at ha hb
  have hProduct : (nearIdentityFraction a - 1) * ((a : Real) - b) = 0 := by
    nlinarith only [ha, hb]
  have hNot : Not (nearIdentityFraction a - 1 = 0) := by
    have hh := (nearIdentityFraction_bounds a).2
    linarith only [hh]
  have hReal := sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_left hNot)
  exact_mod_cast hReal

theorem nearIdentityPoint_parameter_injective (z : Complex) (hz : Not (z = 1)) :
    Function.Injective (fun j : Nat => nearIdentityPoint j z) := by
  intro a b h
  have hProduct : (((nearIdentityFraction a - nearIdentityFraction b : Real) : Complex)) *
      (z - 1) = 0 := by
    unfold nearIdentityPoint at h
    push_cast
    linear_combination h
  have hNot : Not (z - 1 = 0) := sub_ne_zero.mpr hz
  have hCast := (mul_eq_zero.mp hProduct).resolve_right hNot
  have hReal : nearIdentityFraction a - nearIdentityFraction b = 0 := by exact_mod_cast hCast
  exact nearIdentityFraction_injective (sub_eq_zero.mp hReal)

theorem nearIdentityPoint_bounds (j : Nat) (z : Complex) (s H : Real)
    (hs : s <= z.re) (hHi : z.re < 1) (hH : 0 <= H) (hHeight : abs z.im <= H) :
    And (s <= (nearIdentityPoint j z).re)
      (And ((nearIdentityPoint j z).re < 1) (abs (nearIdentityPoint j z).im <= H)) := by
  have ht := nearIdentityFraction_bounds j
  have hre : (nearIdentityPoint j z).re = nearIdentityFraction j * z.re + 1 -
      nearIdentityFraction j := by simp [nearIdentityPoint]; ring
  have him : (nearIdentityPoint j z).im = nearIdentityFraction j * z.im := by
    simp [nearIdentityPoint]
  have hlo := mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr hHi.le)
  have hUpper := mul_pos ht.1 (sub_pos.mpr hHi)
  refine And.intro (by nlinarith only [hre, hs, hlo]) (And.intro ?_ ?_)
  . nlinarith only [hre, hUpper]
  . rw [him, abs_mul, abs_of_pos ht.1]
    have hFirst := mul_le_mul_of_nonneg_left hHeight ht.1.le
    have hSecond := mul_nonneg (sub_nonneg.mpr ht.2.le) hH
    nlinarith only [hFirst, hSecond]

theorem nearIdentityPoint_inverse_lower (j : Nat) (z : Complex) (s : Real)
    (hsPos : 0 < s) (hs : s <= z.re) (hHi : z.re < 1)
    (H : Real) (hH : 0 <= H) (hHeight : abs z.im <= H) :
    s / (1 + H ^ 2) <= (Inv.inv (nearIdentityPoint j z)).re := by
  let w := nearIdentityPoint j z
  have hw := nearIdentityPoint_bounds j z s H hs hHi hH hHeight
  have hwPos : 0 < w.re := lt_of_lt_of_le hsPos hw.1
  have hReProduct := mul_nonneg (sub_nonneg.mpr hw.2.1.le) (by linarith only [hwPos] : 0 <= 1 + w.re)
  have hImBounds := abs_le.mp hw.2.2
  have hImProduct := mul_nonneg (sub_nonneg.mpr hImBounds.2)
    (by linarith only [hImBounds.1] : 0 <= H + w.im)
  have hNormUpper : Complex.normSq w <= 1 + H ^ 2 := by
    change w.re * w.re + w.im * w.im <= 1 + H ^ 2
    nlinarith only [hReProduct, hImProduct]
  have hNormPos : 0 < Complex.normSq w := by
    change 0 < w.re * w.re + w.im * w.im
    exact add_pos_of_pos_of_nonneg (mul_pos hwPos hwPos) (mul_self_nonneg _)
  have hInvNonneg : 0 <= (Inv.inv w).re := by
    rw [Complex.inv_re]
    exact div_nonneg hwPos.le hNormPos.le
  have hInverseIdentity : (Inv.inv w).re * Complex.normSq w = w.re := by
    rw [Complex.inv_re]
    field_simp [hNormPos.ne']
  have hDen : 0 < 1 + H ^ 2 := by nlinarith only [sq_nonneg H]
  have hScale : s / (1 + H ^ 2) * (1 + H ^ 2) = s := by field_simp [hDen.ne']
  have hWeighted : s <= (Inv.inv w).re * (1 + H ^ 2) := by
    calc
      s <= w.re := hw.1
      _ = (Inv.inv w).re * Complex.normSq w := hInverseIdentity.symm
      _ <= (Inv.inv w).re * (1 + H ^ 2) :=
        mul_le_mul_of_nonneg_left hNormUpper hInvNonneg
  by_contra h
  have hStrict := lt_of_not_ge h
  have hProduct := mul_pos (sub_pos.mpr hStrict) hDen
  nlinarith only [hScale, hWeighted, hProduct]

theorem realPowerResidueCoefficient_nonneg (d : Real) (hd : 1 < d)
    (z : Complex) (hRe : 0 <= z.re) :
    0 <= ((d : Complex) * z / (z + (d : Complex) - 1)).re := by
  have hdPos : 0 <= d := by linarith only [hd]
  have hReal : 0 <= ((d : Complex) * z).re * (z + (d : Complex) - 1).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.add_re, Complex.one_re, zero_mul, sub_zero]
    exact mul_nonneg (mul_nonneg hdPos hRe) (by linarith only [hd, hRe])
  have hImag : 0 <= ((d : Complex) * z).im * (z + (d : Complex) - 1).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_im, Complex.add_im, Complex.one_im, sub_zero, add_zero]
    have h := mul_nonneg hdPos (mul_self_nonneg z.im)
    nlinarith only [h]
  rw [Complex.div_re]
  exact add_nonneg (div_nonneg hReal (Complex.normSq_nonneg _))
    (div_nonneg hImag (Complex.normSq_nonneg _))

theorem realPowerResidueCode_target_lower (d : Real) (hd : 1 < d)
    (z : Complex) (hRe : 0 <= z.re) (a b : Int) (hb : 0 <= b) :
    -(a : Real) <= (realPowerResidueCode d z a b).re := by
  have hCoef := realPowerResidueCoefficient_nonneg d hd z hRe
  have hbR : (0 : Real) <= b := by exact_mod_cast hb
  have hSupply := mul_nonneg hCoef hbR
  rw [realPowerResidueCode_real_decomposition]
  unfold realPowerResidueDefect
  nlinarith only [hSupply]

end Complex
