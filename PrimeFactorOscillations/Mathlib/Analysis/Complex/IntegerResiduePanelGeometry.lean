/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueStrip

/-!
# Nonresonant geometry for joint multiplicity panels

Every nonresonant degree >= 3 row has unit norm separation throughout
the closed strip at height >= 2. The complete numerator is retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

private theorem panel_den_pos (d : Nat) (z : Complex) (hH : 2 <= abs z.im) :
    0 < norm (z + (d : Complex) - 1) := by
  have h := Complex.abs_im_le_norm (z + (d : Complex) - 1)
  simp at h
  linarith

theorem integerResidueCode_numerator_re (d : Nat) (z : Complex) (a b : Int)
    (hden : Not (z + (d : Complex) - 1 = 0)) :
    (integerResidueCode d z a b * (z + (d : Complex) - 1)).re =
      (((d : Int) * b - a : Int) : Real) * (z.re + (d : Real) - 1) -
        (d : Real) * ((d : Real) - 1) * (b : Real) := by
  rw [integerResidueCode_mul_den d z a b hden]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.intCast_re, Complex.intCast_im,
    Complex.one_re, Complex.one_im]
  push_cast
  ring

private theorem panel_positive_nonresonant_unit (d : Nat) (hd : 3 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a b : Int) (hk : 1 <= (d : Int) * b - a) :
    1 <= norm (integerResidueCode d z a b) := by
  let k := (d : Int) * b - a
  let q := (k : Real)
  let H := abs z.im
  let D := norm (z + (d : Complex) - 1)
  let w := integerResidueCode d z a b * (z + (d : Complex) - 1)
  change 1 <= k at hk
  have hdR : (3 : Real) <= d := by exact_mod_cast hd
  have hd0 : (0 : Real) <= d := by positivity
  have hq : 1 <= q := by change (1 : Real) <= (k : Real); exact_mod_cast hk
  have hq0 : 0 <= q := by linarith
  have hH0 : 0 <= H := abs_nonneg _
  have hH2 : 2 <= H := hH
  have hHs : H ^ 2 = z.im ^ 2 := sq_abs _
  have hD : 0 < D := panel_den_pos d z hH
  have hN0 : 0 <= norm w := norm_nonneg _
  have hden : Not (z + (d : Complex) - 1 = 0) := norm_pos_iff.mp hD
  have hWN : norm w = norm (integerResidueCode d z a b) * D := norm_mul _ _
  have hR : w.re = q * (z.re + (d : Real) - 1) -
      (d : Real) * ((d : Real) - 1) * (b : Real) :=
    integerResidueCode_numerator_re d z a b hden
  have hI : w.im = q * z.im := integerResidueCode_integer_im d z a b hden
  have hNs : norm w ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hDs : D ^ 2 = (z.re + (d : Real) - 1) ^ 2 + z.im ^ 2 := by
    dsimp [D]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hx0 : 0 <= z.re + (d : Real) - 1 := by linarith [hRe.1]
  have hxD : z.re + (d : Real) - 1 <= d := by linarith [hRe.2]
  have hDSq : D ^ 2 <= (d : Real) ^ 2 + H ^ 2 := by nlinarith only [hDs, hx0, hxD, hHs, hd0]
  have hIm : q * H <= norm w := by
    have h := Complex.abs_im_le_norm w
    rw [hI, abs_mul, abs_of_nonneg hq0] at h
    exact h
  have hND : D <= norm w := by
    by_cases hkBig : (d : Int) - 1 <= k
    . have hkR : (d : Real) - 1 <= q := by
        change (d : Real) - 1 <= (k : Real)
        exact_mod_cast hkBig
      have hm := mul_le_mul_of_nonneg_right hkR hH0
      have hLow : ((d : Real) - 1) * H <= norm w := hm.trans hIm
      have hLow0 : 0 <= ((d : Real) - 1) * H :=
        mul_nonneg (by linarith) hH0
      have hPow : (((d : Real) - 1) * H) ^ 2 <= norm w ^ 2 := by
        nlinarith only [hLow, hLow0, hN0]
      have hHsq : 4 <= H ^ 2 := by nlinarith only [hH2]
      have hBase : (d : Real) ^ 2 <= 4 * (d : Real) * ((d : Real) - 2) := by
        nlinarith only [mul_nonneg hd0 (by linarith : 0 <= 3 * (d : Real) - 8)]
      have hProd := mul_le_mul_of_nonneg_left hHsq
        (mul_nonneg hd0 (by linarith : 0 <= (d : Real) - 2))
      nlinarith only [hPow, hBase, hProd, hDSq, hD, hN0]
    . have hkTop : k <= (d : Int) - 2 := by omega
      have hkR : q <= (d : Real) - 2 := by
        change (k : Real) <= (d : Real) - 2
        exact_mod_cast hkTop
      by_cases hb : b = 0
      . have ha : (a : Int) <= -1 := by dsimp [k] at hk; simp [hb] at hk; omega
        have haR : (a : Real) <= -1 := by exact_mod_cast ha
        have hc := Complex.abs_re_le_norm (integerResidueCode d z a b)
        have he : (integerResidueCode d z a b).re = -(a : Real) := by
          simp [integerResidueCode, hb]
        rw [he] at hc
        have hOne : 1 <= norm (integerResidueCode d z a b) := by
          nlinarith only [hc, le_abs_self (-(a : Real)), haR]
        rw [hWN]
        simpa using mul_le_mul_of_nonneg_right hOne hD.le
      . have hReal : Or (w.re <= -(d : Real)) ((d : Real) <= w.re) := by
          rcases lt_or_gt_of_ne hb with hn | hp
          . have hbN : b <= -1 := by omega
            have hbR : (b : Real) <= -1 := by exact_mod_cast hbN
            have hPos := mul_nonneg hq0 hx0
            have hMul := mul_le_mul_of_nonneg_left hbR
              (mul_nonneg hd0 (by linarith : 0 <= (d : Real) - 1))
            have hdP : (d : Real) <= (d : Real) * ((d : Real) - 1) := by
              nlinarith only [mul_nonneg hd0 (by linarith : 0 <= (d : Real) - 2)]
            exact Or.inr (by nlinarith only [hR, hPos, hMul, hdP])
          . have hbN : (1 : Int) <= b := by omega
            have hbR : (1 : Real) <= (b : Real) := by exact_mod_cast hbN
            have hFirst := mul_le_mul_of_nonneg_left hxD hq0
            have hSecond := mul_le_mul_of_nonneg_right hkR hd0
            have hMul := mul_le_mul_of_nonneg_left hbR
              (mul_nonneg hd0 (by linarith : 0 <= (d : Real) - 1))
            exact Or.inl (by nlinarith only [hR, hFirst, hSecond, hMul])
        have hRealSq : (d : Real) ^ 2 <= w.re ^ 2 := by
          rcases hReal with hn | hp
          . nlinarith only [hn, hd0]
          . nlinarith only [hp, hd0]
        have hIH : H <= q * H := by nlinarith only [mul_nonneg (by linarith : 0 <= q - 1) hH0]
        have hISq : H ^ 2 <= w.im ^ 2 := by
          have he : w.im ^ 2 = (q * H) ^ 2 := by rw [hI, mul_pow, mul_pow, hHs]
          nlinarith only [he, hIH, hH0]
        nlinarith only [hRealSq, hISq, hNs, hDSq, hD, hN0]
  exact le_of_mul_le_mul_right (by rw [one_mul, <- hWN]; exact hND) hD

theorem integerResidueCode_nonresonant_unit (d : Nat) (hd : 3 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a b : Int) (hk : Not ((d : Int) * b - a = 0)) :
    1 <= norm (integerResidueCode d z a b) := by
  rcases lt_or_gt_of_ne hk with hn | hp
  . have hNeg : 1 <= (d : Int) * (-b) - (-a) := by nlinarith only [hn]
    have h := panel_positive_nonresonant_unit d hd z hRe hH (-a) (-b) hNeg
    have he : integerResidueCode d z (-a) (-b) = -integerResidueCode d z a b := by
      unfold integerResidueCode
      push_cast
      ring
    simpa only [he, norm_neg] using h
  . have hPos : 1 <= (d : Int) * b - a := by omega
    exact panel_positive_nonresonant_unit d hd z hRe hH a b hPos

private theorem panel_two_positive_unit (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a b : Int) (hk : 1 <= 2 * b - a)
    (haPos : Not (a = 1)) (haNeg : Not (a = -1)) :
    1 <= norm (integerResidueCode 2 z a b) := by
  let k := 2 * b - a
  let q := (k : Real)
  let H := abs z.im
  let D := norm (z + (2 : Complex) - 1)
  let w := integerResidueCode 2 z a b * (z + (2 : Complex) - 1)
  change 1 <= k at hk
  have hq : 1 <= q := by change (1 : Real) <= (k : Real); exact_mod_cast hk
  have hq0 : 0 <= q := by linarith
  have hH0 : 0 <= H := abs_nonneg _
  have hH2 : 2 <= H := hH
  have hHs : H ^ 2 = z.im ^ 2 := sq_abs _
  have hHsq : 4 <= H ^ 2 := by nlinarith only [hH2]
  have hD : 0 < D := panel_den_pos 2 z hH
  have hN0 : 0 <= norm w := norm_nonneg _
  have hden : Not (z + (2 : Complex) - 1 = 0) := norm_pos_iff.mp hD
  have hWN : norm w = norm (integerResidueCode 2 z a b) * D := norm_mul _ _
  have hR : w.re = q * (z.re + 1) - 2 * (b : Real) := by
    have h := integerResidueCode_numerator_re 2 z a b hden
    calc
      w.re = (k : Real) * (z.re + (2 : Real) - 1) -
          (2 : Real) * ((2 : Real) - 1) * (b : Real) := h
      _ = q * (z.re + 1) - 2 * (b : Real) := by dsimp [q]; ring
  have hI : w.im = q * z.im := integerResidueCode_integer_im 2 z a b hden
  have hNs : norm w ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hDs : D ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
    dsimp [D]
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num
    ring
  have hDSq : D ^ 2 <= 4 + H ^ 2 := by nlinarith only [hDs, hHs, hRe.1, hRe.2]
  have hND : D <= norm w := by
    by_cases hkBig : (2 : Int) <= k
    . have hq2 : (2 : Real) <= q := by change (2 : Real) <= (k : Real); exact_mod_cast hkBig
      have hm := mul_le_mul_of_nonneg_right hq2 hH0
      have he : w.im ^ 2 = (q * H) ^ 2 := by rw [hI, mul_pow, mul_pow, hHs]
      have hISq : 4 * H ^ 2 <= w.im ^ 2 := by nlinarith only [hm, hH0, he]
      nlinarith only [hNs, hDSq, hISq, hHsq, sq_nonneg w.re, hD, hN0]
    . have hkOne : k = 1 := by omega
      have hqOne : q = 1 := by change (k : Real) = 1; exact_mod_cast hkOne
      have hb0 : Not (b = 0) := by
        intro hb
        apply haNeg
        dsimp [k] at hkOne
        omega
      have hb1 : Not (b = 1) := by
        intro hb
        apply haPos
        dsimp [k] at hkOne
        omega
      rw [hqOne] at hR
      rw [hqOne, one_mul] at hI
      have hReal : Or (w.re <= -2) (2 <= w.re) := by
        rcases lt_or_gt_of_ne hb0 with hn | hp
        . have hbN : b <= -1 := by omega
          have hbR : (b : Real) <= -1 := by exact_mod_cast hbN
          exact Or.inr (by nlinarith only [hR, hbR, hRe.1])
        . have hbN : (2 : Int) <= b := by omega
          have hbR : (2 : Real) <= (b : Real) := by exact_mod_cast hbN
          exact Or.inl (by nlinarith only [hR, hbR, hRe.2])
      have hRSq : 4 <= w.re ^ 2 := by
        rcases hReal with hn | hp
        . nlinarith only [hn]
        . nlinarith only [hp]
      have hISq : w.im ^ 2 = H ^ 2 := by rw [hI, <- hHs]
      nlinarith only [hNs, hDSq, hRSq, hISq, hD, hN0]
  exact le_of_mul_le_mul_right (by rw [one_mul, <- hWN]; exact hND) hD

theorem integerResidueCode_two_nonresonant_unit (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a b : Int) (hk : Not (2 * b - a = 0))
    (haPos : Not (a = 1)) (haNeg : Not (a = -1)) :
    1 <= norm (integerResidueCode 2 z a b) := by
  rcases lt_or_gt_of_ne hk with hn | hp
  . have hNeg : 1 <= 2 * (-b) - (-a) := by nlinarith only [hn]
    have haNPos : Not (-a = 1) := by omega
    have haNNeg : Not (-a = -1) := by omega
    have h := panel_two_positive_unit z hRe hH (-a) (-b) hNeg haNPos haNNeg
    have he : integerResidueCode 2 z (-a) (-b) = -integerResidueCode 2 z a b := by
      unfold integerResidueCode
      push_cast
      ring
    simpa only [he, norm_neg] using h
  . have hPos : 1 <= 2 * b - a := by omega
    exact panel_two_positive_unit z hRe hH a b hPos haPos haNeg

theorem integerResidueCode_resonant_norm (d : Nat) (hd : 2 <= d)
    (z : Complex) (hH : 2 <= abs z.im) (a b : Int) (hk : (d : Int) * b = a) :
    norm (integerResidueCode d z a b) =
      abs (a : Real) * ((d : Real) - 1) / norm (z + (d : Complex) - 1) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hd1 : 0 <= (d : Real) - 1 := by linarith
  have hD := panel_den_pos d z hH
  have hden : Not (z + (d : Complex) - 1 = 0) := norm_pos_iff.mp hD
  have hkC : (d : Complex) * (b : Complex) - (a : Complex) = 0 := by
    exact_mod_cast (sub_eq_zero.mpr hk)
  have h := integerResidueCode_mul_den d z a b hden
  rw [hkC, mul_zero, zero_sub] at h
  have hc : (d : Complex) - 1 = (((d : Real) - 1 : Real) : Complex) := by
    apply Complex.ext <;> simp
  have hn := congrArg norm h
  simp only [norm_mul, norm_neg, hc, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_intCast, abs_of_nonneg hd1] at hn
  apply (eq_div_iff hD.ne').mpr
  exact hn.trans (mul_comm _ _)

theorem residueReferenceFraction_mono (d e : Nat) (hd : 2 <= d) (hde : d <= e)
    (z : Complex) (hRe : 0 <= z.re) (hH : 2 <= abs z.im) :
    ((d : Real) - 1) / norm (z + (d : Complex) - 1) <=
      ((e : Real) - 1) / norm (z + (e : Complex) - 1) := by
  let t := (d : Real) - 1
  let u := (e : Real) - 1
  let Dd := norm (z + (d : Complex) - 1)
  let De := norm (z + (e : Complex) - 1)
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hdeR : (d : Real) <= e := by exact_mod_cast hde
  have ht : 0 <= t := by dsimp [t]; linarith
  have hu : 0 <= u := by dsimp [u]; linarith
  have htu : t <= u := by dsimp [t, u]; linarith
  have hDd : 0 < Dd := panel_den_pos d z hH
  have hDe : 0 < De := panel_den_pos e z hH
  have hDs : Dd ^ 2 = (z.re + t) ^ 2 + z.im ^ 2 := by
    dsimp [Dd, t]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hEs : De ^ 2 = (z.re + u) ^ 2 + z.im ^ 2 := by
    dsimp [De, u]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hInner : 0 <= 2 * t * u * z.re + (z.re ^ 2 + z.im ^ 2) * (u + t) := by positivity
  have hProd := mul_nonneg (sub_nonneg.mpr htu) hInner
  have heq : (u * Dd) ^ 2 - (t * De) ^ 2 =
      (u - t) * (2 * t * u * z.re + (z.re ^ 2 + z.im ^ 2) * (u + t)) := by
    rw [mul_pow, mul_pow, hDs, hEs]
    ring
  have hCrossSq : (t * De) ^ 2 <= (u * Dd) ^ 2 := by nlinarith only [hProd, heq]
  have hCross : t * De <= u * Dd := by
    nlinarith only [hCrossSq, mul_nonneg ht hDe.le, mul_nonneg hu hDd.le]
  have hLeft : (t / Dd) * (Dd * De) = t * De := by field_simp [hDd.ne'] <;> ring
  have hRight : (u / De) * (Dd * De) = u * Dd := by field_simp [hDe.ne'] <;> ring
  have hm : (t / Dd) * (Dd * De) <= (u / De) * (Dd * De) := by
    rw [hLeft, hRight]
    exact hCross
  exact le_of_mul_le_mul_right hm (mul_pos hDd hDe)

end Complex

end
