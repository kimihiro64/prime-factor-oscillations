/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueAdaptive

/-!
# Exact compensated residue spacing throughout the strip

The oblique rows are retained. For every d >= 2 and height >= 2, the
shortest nonzero integer residue has norm min(1, d*(d-1)/norm(z+d-1)).
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

private theorem strip_int_abs_one (a : Int) (ha : Not (a = 0)) :
    (1 : Real) <= abs (a : Real) := by
  have hi : (1 : Int) <= abs a := by
    rcases lt_or_gt_of_ne ha with hn | hp
    . rw [abs_of_neg hn]
      omega
    . rw [abs_of_pos hp]
      omega
  exact_mod_cast hi

private theorem strip_den_ne (d : Nat) (z : Complex)
    (hH : 2 <= abs z.im) : Not (z + (d : Complex) - 1 = 0) := by
  intro he
  have hi := congrArg Complex.im he
  simp at hi
  rw [hi, abs_zero] at hH
  linarith

theorem integerResidueReference_half (d : Nat) (hd : 2 <= d) (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (hUpper : abs z.im <= (d : Real) * ((d : Real) - 1)) :
    1 / 2 <= abs (((d : Complex) * z / (z + (d : Complex) - 1)).im) := by
  let H := abs z.im
  let x := z.re + (d : Real) - 1
  let p := (d : Real) * ((d : Real) - 1)
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hd0 : (0 : Real) <= d := by positivity
  have hd1 : 0 <= (d : Real) - 1 := by linarith
  have hp : 0 <= p := mul_nonneg hd0 hd1
  have hH0 : 0 <= H := abs_nonneg _
  have hHs : H ^ 2 = z.im ^ 2 := sq_abs _
  have hx0 : 0 <= x := by dsimp [x]; linarith [hRe.1]
  have hxD : x <= d := by dsimp [x]; linarith [hRe.2]
  have hxSq : x ^ 2 <= (d : Real) ^ 2 := by nlinarith
  have hdSq : (d : Real) ^ 2 <= 2 * p := by
    dsimp [p]
    nlinarith [mul_nonneg hd0 (by linarith : 0 <= (d : Real) - 2)]
  have hFirst : (d : Real) ^ 2 <= p * H := by
    have hm := mul_le_mul_of_nonneg_left hH hp
    nlinarith
  have hSecond : H ^ 2 <= p * H := by
    have hm := mul_le_mul_of_nonneg_right hUpper hH0
    change H * H <= p * H at hm
    nlinarith
  have hDen : 0 < x ^ 2 + z.im ^ 2 := by
    change 2 <= H at hH
    nlinarith [sq_nonneg x]
  have hBound : x ^ 2 + z.im ^ 2 <= 2 * p * H := by nlinarith
  have hDiv := div_le_div_of_nonneg_right hBound hDen.le
  rw [div_self hDen.ne'] at hDiv
  rw [integerResidueReference_im, abs_div, abs_mul, abs_mul,
    abs_of_nonneg hd0, abs_of_nonneg hd1, abs_of_pos hDen]
  change 1 / 2 <= p * H / (x ^ 2 + z.im ^ 2)
  have he : (2 * p * H) / (x ^ 2 + z.im ^ 2) =
      2 * (p * H / (x ^ 2 + z.im ^ 2)) := by ring
  rw [he] at hDiv
  linarith

private theorem strip_row_one (d : Nat) (hd : 3 <= d) (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im) (a : Int) :
    min (norm (z + (d : Complex) - 1)) ((d : Real) * ((d : Real) - 1)) <=
      norm (integerResidueCode d z a 1) * norm (z + (d : Complex) - 1) := by
  let D := norm (z + (d : Complex) - 1)
  let p := (d : Real) * ((d : Real) - 1)
  let H := abs z.im
  let w := integerResidueCode d z a 1 * (z + (d : Complex) - 1)
  have hdR : (3 : Real) <= d := by exact_mod_cast hd
  have hd0 : (0 : Real) <= d := by positivity
  have hH0 : 0 <= H := abs_nonneg _
  have hHs : H ^ 2 = z.im ^ 2 := sq_abs _
  have hD0 : 0 <= D := norm_nonneg _
  have hN0 : 0 <= norm w := norm_nonneg _
  have hW : norm w = norm (integerResidueCode d z a 1) * D := norm_mul _ _
  have hR : w.re = ((d : Real) - (a : Real)) * z.re -
      ((d : Real) - 1) * (a : Real) := by
    dsimp [w]
    rw [integerResidueCode_mul_den d z a 1 (strip_den_ne d z hH)]
    simp [Complex.mul_re]
    ring
  have hI : w.im = ((d : Real) - (a : Real)) * z.im := by
    dsimp [w]
    rw [integerResidueCode_mul_den d z a 1 (strip_den_ne d z hH)]
    simp [Complex.mul_im]
    ring
  have hDs : D ^ 2 = (z.re + (d : Real) - 1) ^ 2 + z.im ^ 2 := by
    dsimp [D]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hNs : norm w ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hx0 : 0 <= z.re + (d : Real) - 1 := by linarith [hRe.1]
  have hxD : z.re + (d : Real) - 1 <= d := by linarith [hRe.2]
  have hDSq : D ^ 2 <= (d : Real) ^ 2 + H ^ 2 := by nlinarith
  have hDTri : D <= (d : Real) + H := by
    have h := Complex.norm_le_abs_re_add_abs_im (z + (d : Complex) - 1)
    simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.natCast_im, Complex.one_im,
      add_zero, sub_zero] at h
    rw [abs_of_nonneg hx0] at h
    change D <= z.re + (d : Real) - 1 + H at h
    linarith [hRe.2]
  by_cases ha : (d : Int) <= a
  . have haR : (d : Real) <= (a : Real) := by exact_mod_cast ha
    have hk := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr haR) hRe.1
    have hm := mul_le_mul_of_nonneg_left haR (by linarith : 0 <= (d : Real) - 1)
    have hr : w.re <= -p := by dsimp [p]; nlinarith
    have hn : p <= norm w := by
      have hn := Complex.abs_re_le_norm w
      have hp := neg_le_abs w.re
      linarith
    rw [<- hW]
    exact (min_le_right D p).trans hn
  . have haTop : a <= (d : Int) - 1 := by omega
    have haTopR : (a : Real) <= (d : Real) - 1 := by exact_mod_cast haTop
    have hk0 : 0 <= (d : Real) - (a : Real) := by linarith
    have hIm : ((d : Real) - (a : Real)) * H <= norm w := by
      have h := Complex.abs_im_le_norm w
      rw [hI, abs_mul, abs_of_nonneg hk0] at h
      exact h
    have hDN : D <= norm w := by
      by_cases ha0 : a <= 0
      . have ha0R : (a : Real) <= 0 := by exact_mod_cast ha0
        have hP := mul_nonneg (by linarith : 0 <= (d : Real) - 2)
          (by change 0 <= H - 2; change 2 <= H at hH; linarith)
        have hA := mul_nonneg (by linarith : 0 <= -(a : Real)) hH0
        change 2 <= H at hH
        nlinarith
      . by_cases ha1 : a = 1
        . have ha1R : (a : Real) = 1 := by simp [ha1]
          have hHsq : 4 <= H ^ 2 := by change 2 <= H at hH; nlinarith
          have hBase : (d : Real) ^ 2 <= 4 * (d : Real) * ((d : Real) - 2) := by
            nlinarith [mul_nonneg hd0 (by linarith : 0 <= 3 * (d : Real) - 8)]
          have hProd := mul_le_mul_of_nonneg_left hHsq
            (mul_nonneg hd0 (by linarith : 0 <= (d : Real) - 2))
          have hImSq : w.im ^ 2 = ((d : Real) - 1) ^ 2 * H ^ 2 := by
            rw [hI, ha1R, mul_pow, hHs]
          nlinarith only [hNs, hDSq, hImSq, hBase, hProd, hD0, hN0, sq_nonneg w.re]
        . have ha2 : (2 : Int) <= a := by omega
          have ha2R : (2 : Real) <= (a : Real) := by exact_mod_cast ha2
          have hK := mul_le_mul_of_nonneg_left hRe.2 hk0
          have hA := mul_nonneg hd0 (by linarith : 0 <= (a : Real) - 2)
          have hReal : w.re <= -(d : Real) := by nlinarith only [hR, hK, hA]
          have hRealSq : (d : Real) ^ 2 <= w.re ^ 2 := by nlinarith only [hReal, hd0]
          have hk1 : 1 <= (d : Real) - (a : Real) := by linarith
          have hHK := mul_le_mul_of_nonneg_right hk1 hH0
          have hImSq : H ^ 2 <= w.im ^ 2 := by
            have he : w.im ^ 2 = (((d : Real) - (a : Real)) * H) ^ 2 := by
              rw [hI, mul_pow, mul_pow, hHs]
            nlinarith only [he, hHK, hH0]
          nlinarith only [hNs, hDSq, hRealSq, hImSq, hD0, hN0]
    rw [<- hW]
    exact (min_le_left D p).trans hDN

theorem integerResidueCode_strip_scaled_separation (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a b : Int) (hab : Not (And (a = 0) (b = 0))) :
    min (norm (z + (d : Complex) - 1)) ((d : Real) * ((d : Real) - 1)) <=
      norm (integerResidueCode d z a b) * norm (z + (d : Complex) - 1) := by
  by_cases hHigh : (d : Real) * ((d : Real) - 1) <= abs z.im
  . exact (min_le_right _ _).trans
      (integerResidueCode_separation d hd z hHigh a b hab (strip_den_ne d z hH))
  . have hd3 : 3 <= d := by
      by_contra hn
      have he : d = 2 := by omega
      subst d
      norm_num at hHigh
      linarith
    have hHalf := integerResidueReference_half d hd z hRe hH (le_of_lt (lt_of_not_ge hHigh))
    by_cases hb0 : b = 0
    . have ha : Not (a = 0) := by intro he; exact hab (And.intro he hb0)
      have hn : 1 <= norm (integerResidueCode d z a b) := by
        simpa [integerResidueCode, hb0] using strip_int_abs_one a ha
      exact (min_le_left _ _).trans (by nlinarith [norm_nonneg (z + (d : Complex) - 1)])
    . by_cases hb1 : b = 1
      . subst b
        exact strip_row_one d hd3 z hRe hH a
      . by_cases hbNeg : b = -1
        . have he : integerResidueCode d z a b = -integerResidueCode d z (-a) 1 := by
            subst b
            unfold integerResidueCode
            push_cast
            ring
          rw [he, norm_neg]
          exact strip_row_one d hd3 z hRe hH (-a)
        . have hbI : (2 : Int) <= abs b := by
            rcases le_total b 0 with hn | hp
            . rw [abs_of_nonpos hn]
              omega
            . rw [abs_of_nonneg hp]
              omega
          have hbR : (2 : Real) <= abs (b : Real) := by exact_mod_cast hbI
          have hn := Complex.abs_im_le_norm (integerResidueCode d z a b)
          rw [integerResidueCode_im, abs_mul] at hn
          have hp := mul_le_mul hHalf hbR (by norm_num) (abs_nonneg _)
          have hOne : 1 <= norm (integerResidueCode d z a b) := by nlinarith
          exact (min_le_left _ _).trans
            (by nlinarith [norm_nonneg (z + (d : Complex) - 1)])

theorem integerResidueCode_strip_separation (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a b : Int) (hab : Not (And (a = 0) (b = 0))) :
    min 1 ((d : Real) * ((d : Real) - 1) / norm (z + (d : Complex) - 1)) <=
      norm (integerResidueCode d z a b) := by
  let D := norm (z + (d : Complex) - 1)
  let p := (d : Real) * ((d : Real) - 1)
  have hD : 0 < D := norm_pos_iff.mpr (strip_den_ne d z hH)
  have h := integerResidueCode_strip_scaled_separation d hd z hRe hH a b hab
  change min D p <= norm (integerResidueCode d z a b) * D at h
  have he : (p / D) * D = p := by field_simp
  by_cases hp : D <= p
  . have hOne : 1 <= p / D :=
      le_of_mul_le_mul_right (by rw [one_mul, he]; exact hp) hD
    rw [min_eq_left hOne]
    rw [min_eq_left hp] at h
    exact le_of_mul_le_mul_right (by simpa using h) hD
  . have hpD : p <= D := le_of_lt (lt_of_not_ge hp)
    have hOne : p / D <= 1 :=
      le_of_mul_le_mul_right (by rw [one_mul, he]; exact hpD) hD
    rw [min_eq_right hOne]
    rw [min_eq_right hpD] at h
    exact le_of_mul_le_mul_right (by rw [he]; exact h) hD

theorem integerResidueCode_strip_pair_separation (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a b a' b' : Int) (hab : Not (And (a = a') (b = b'))) :
    min 1 ((d : Real) * ((d : Real) - 1) / norm (z + (d : Complex) - 1)) <=
      norm (integerResidueCode d z a b - integerResidueCode d z a' b') := by
  rw [integerResidueCode_sub]
  apply integerResidueCode_strip_separation d hd z hRe hH
  intro h
  exact hab (And.intro (by omega) (by omega))

theorem integerResidueCode_strip_attains (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im) :
    Exists (fun a : Int => Exists (fun b : Int =>
      And (Not (And (a = 0) (b = 0)))
        (norm (integerResidueCode d z a b) =
          min 1 ((d : Real) * ((d : Real) - 1) / norm (z + (d : Complex) - 1))))) := by
  let D := norm (z + (d : Complex) - 1)
  let p := (d : Real) * ((d : Real) - 1)
  have hD : 0 < D := norm_pos_iff.mpr (strip_den_ne d z hH)
  have he : (p / D) * D = p := by field_simp
  by_cases hp : D <= p
  . have hOne : 1 <= p / D :=
      le_of_mul_le_mul_right (by rw [one_mul, he]; exact hp) hD
    refine Exists.intro 1 (Exists.intro 0 (And.intro ?_ ?_))
    . norm_num
    . change norm (integerResidueCode d z 1 0) = min 1 (p / D)
      rw [min_eq_left hOne, integerResidueCode_unit_attains]
  . have hpD : p <= D := le_of_lt (lt_of_not_ge hp)
    have hOne : p / D <= 1 :=
      le_of_mul_le_mul_right (by rw [one_mul, he]; exact hpD) hD
    refine Exists.intro (d : Int) (Exists.intro 1 (And.intro ?_ ?_))
    . intro h
      norm_num at h
    . change norm (integerResidueCode d z (d : Int) 1) = min 1 (p / D)
      rw [min_eq_right hOne]
      have h := integerResidueCode_attains d hd z (strip_den_ne d z hH)
      change norm (integerResidueCode d z (d : Int) 1) * D = p at h
      apply le_antisymm
      . exact le_of_mul_le_mul_right (le_of_eq (h.trans he.symm)) hD
      . exact le_of_mul_le_mul_right (le_of_eq (he.trans h.symm)) hD

theorem integerResidueCode_strip_unit_iff (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im) :
    (forall a b : Int, Not (And (a = 0) (b = 0)) ->
      1 <= norm (integerResidueCode d z a b)) <->
      norm (z + (d : Complex) - 1) <= (d : Real) * ((d : Real) - 1) := by
  constructor
  . intro h
    have hOne := h (d : Int) 1 (by intro he; norm_num at he)
    have hAtt := integerResidueCode_attains d hd z (strip_den_ne d z hH)
    have hm := mul_le_mul_of_nonneg_right hOne (norm_nonneg (z + (d : Complex) - 1))
    simpa only [one_mul, hAtt] using hm
  . intro hDisk a b hab
    have hD : 0 < norm (z + (d : Complex) - 1) :=
      norm_pos_iff.mpr (strip_den_ne d z hH)
    have he : (((d : Real) * ((d : Real) - 1)) / norm (z + (d : Complex) - 1)) *
        norm (z + (d : Complex) - 1) = (d : Real) * ((d : Real) - 1) := by field_simp
    have hRatio : 1 <= ((d : Real) * ((d : Real) - 1)) /
        norm (z + (d : Complex) - 1) :=
      le_of_mul_le_mul_right (by rw [one_mul, he]; exact hDisk) hD
    simpa only [min_eq_left hRatio] using
      integerResidueCode_strip_separation d hd z hRe hH a b hab

theorem integerResidueCode_strip_unique (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a b a' b' : Int) (observation : Complex)
    (hErr : norm (integerResidueCode d z a b - observation) +
      norm (integerResidueCode d z a' b' - observation) <
        min 1 ((d : Real) * ((d : Real) - 1) / norm (z + (d : Complex) - 1))) :
    And (a = a') (b = b') := by
  by_contra hNe
  have hSep := integerResidueCode_strip_pair_separation d hd z hRe hH a b a' b' hNe
  have hTri := norm_sub_le (integerResidueCode d z a b - observation)
    (integerResidueCode d z a' b' - observation)
  have he : integerResidueCode d z a b - observation -
      (integerResidueCode d z a' b' - observation) =
      integerResidueCode d z a b - integerResidueCode d z a' b' := by ring
  rw [he] at hTri
  linarith

end Complex

end
