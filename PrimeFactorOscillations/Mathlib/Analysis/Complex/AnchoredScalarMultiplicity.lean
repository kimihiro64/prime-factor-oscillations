/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueStrip

/-!
# Uniform scalar integer recovery from an anchored two-row code

The supporting triangular rounding argument is classical. The exact cubic
projection formula and its one-channel loss serve the actual readout consumer.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

def anchoredScalarFirst (t : Real) (a b : Int) : Real := -(a : Real) + t * (b : Real)

def anchoredScalarNorm (t : Real) (a b : Int) : Real :=
  max (abs (anchoredScalarFirst t a b)) (abs (b : Real))

def anchoredScalarDecode (t y0 y1 : Real) : Prod Int Int :=
  let b := Int.floor (-y1 + (1 / 2 : Real))
  Prod.mk (Int.floor (t * (b : Real) - y0 + (1 / 2 : Real))) b

theorem integerResidueCode_re_scalar (d : Nat) (z : Complex) (a b : Int) :
    (integerResidueCode d z a b).re =
      anchoredScalarFirst (((d : Complex) * z / (z + (d : Complex) - 1)).re) a b := by
  simp [integerResidueCode, anchoredScalarFirst, Complex.mul_re]

theorem anchoredScalar_unit (t : Real) (a b : Int) (hab : Not (And (a = 0) (b = 0))) :
    1 <= anchoredScalarNorm t a b := by
  unfold anchoredScalarNorm
  by_cases hb : b = 0
  . have ha : Not (a = 0) := fun h => hab (And.intro h hb)
    have hInt := Int.one_le_abs ha
    have hR : (1 : Real) <= abs (a : Real) := by exact_mod_cast hInt
    have he : abs (anchoredScalarFirst t a b) = abs (a : Real) := by
      simp [anchoredScalarFirst, hb]
    rw [he]
    exact hR.trans (le_max_left _ _)
  . have hInt := Int.one_le_abs hb
    have hR : (1 : Real) <= abs (b : Real) := by exact_mod_cast hInt
    exact hR.trans (le_max_right _ _)

theorem anchoredScalar_unit_attains (t : Real) : anchoredScalarNorm t 1 0 = 1 := by
  norm_num [anchoredScalarNorm, anchoredScalarFirst]

private theorem anchored_round (x : Real) (a : Int) (h : abs (x - (a : Real)) < 1 / 2) :
    Int.floor (x + (1 / 2 : Real)) = a := by
  apply Int.floor_eq_iff.mpr
  have hh := abs_lt.mp h
  exact And.intro (by linarith) (by linarith)

theorem anchoredScalar_decode (t y0 y1 : Real) (a b : Int)
    (h0 : abs (anchoredScalarFirst t a b - y0) < 1 / 2)
    (h1 : abs (-(b : Real) - y1) < 1 / 2) :
    anchoredScalarDecode t y0 y1 = Prod.mk a b := by
  have hb : Int.floor (-y1 + (1 / 2 : Real)) = b := by
    apply anchored_round (-y1) b
    have he : -y1 - (b : Real) = -(b : Real) - y1 := by ring
    rw [he]
    exact h1
  have ha : Int.floor (t * (b : Real) - y0 + (1 / 2 : Real)) = a := by
    apply anchored_round (t * (b : Real) - y0) a
    have he : t * (b : Real) - y0 - (a : Real) = anchoredScalarFirst t a b - y0 := by
      unfold anchoredScalarFirst
      ring
    rw [he]
    exact h0
  simp only [anchoredScalarDecode, hb, ha]

theorem anchoredScalar_half_noise_sharp (t : Real) :
    And (max (abs (anchoredScalarFirst t 0 0 + 1 / 2)) (0 : Real) = 1 / 2)
      (max (abs (anchoredScalarFirst t 1 0 + 1 / 2)) (0 : Real) = 1 / 2) := by
  norm_num [anchoredScalarFirst]

theorem anchoredScalar_negative_signal (t : Real) (a b : Nat) (hab : 1 <= a + b) :
    min (anchoredScalarFirst t (a : Int) (b : Int)) (-(b : Real)) <= -1 := by
  by_cases hb : b = 0
  . have ha : 1 <= a := by omega
    have haR : (1 : Real) <= a := by exact_mod_cast ha
    have hf : anchoredScalarFirst t (a : Int) (b : Int) <= -1 := by
      simpa [anchoredScalarFirst, hb] using (neg_le_neg haR)
    exact (min_le_left _ _).trans hf
  . have hb1 : 1 <= b := by omega
    have hbR : (1 : Real) <= b := by exact_mod_cast hb1
    exact (min_le_right _ _).trans (by linarith)

theorem cubicScalar_resonance_bound (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im) :
    abs (integerResidueCode 3 z 3 1).re <= 18 / (abs z.im) ^ 2 := by
  let H := abs z.im
  let D := (z.re + 2) ^ 2 + z.im ^ 2
  have hH0 : 0 < H := by change 0 < abs z.im; linarith
  have hHs : H ^ 2 = z.im ^ 2 := sq_abs _
  have hHp : 0 < H ^ 2 := by positivity
  have hD : 0 < D := by dsimp [D]; nlinarith [sq_nonneg (z.re + 2)]
  have hDH : H ^ 2 <= D := by dsimp [D]; nlinarith [sq_nonneg (z.re + 2)]
  have hDen : Not (z + 2 = 0) := by
    intro he
    have hi : z.im = 0 := by simpa using congrArg Complex.im he
    rw [hi, abs_zero] at hH
    linarith
  have hRes : integerResidueCode 3 z 3 1 = (-6 : Complex) / (z + 2) := by
    have he : z + (3 : Complex) - 1 = z + 2 := by ring
    norm_num only [integerResidueCode, Nat.cast_ofNat, Int.cast_ofNat, Int.cast_one]
    rw [he]
    field_simp [hDen]
    ring
  have hForm : (integerResidueCode 3 z 3 1).re = -6 * (z.re + 2) / D := by
    rw [hRes]
    norm_num [Complex.div_re, Complex.normSq_apply, D]
    ring
  have hNeg : -6 * (z.re + 2) / D <= 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith [hRe.1]) hD.le
  let U := 6 * (z.re + 2) / D
  have hU0 : 0 <= U := div_nonneg (by linarith [hRe.1]) hD.le
  have hUD : U * D = 6 * (z.re + 2) := by dsimp [U]; field_simp [ne_of_gt hD]
  have hV : (18 / H ^ 2) * H ^ 2 = (18 : Real) := by field_simp [ne_of_gt hHp]
  have hm := mul_le_mul_of_nonneg_left hDH hU0
  rw [hUD] at hm
  have hSmall : U * H ^ 2 <= 18 := by linarith [hRe.2]
  have hUV : U <= 18 / H ^ 2 :=
    le_of_mul_le_mul_right (by rw [hV]; exact hSmall) hHp
  rw [hForm, abs_of_nonpos hNeg]
  change -(-6 * (z.re + 2) / D) <= 18 / H ^ 2
  have he : -(-6 * (z.re + 2) / D) = U := by dsimp [U]; ring
  rw [he]
  exact hUV

theorem cubicScalar_no_uniform_spacing (eps : Real) (hE : 0 < eps) :
    Exists (fun z : Complex => And (z.re = (1 / 4 : Real))
      (And (2 <= abs z.im) (abs (integerResidueCode 3 z 3 1).re < eps))) := by
  let H : Real := 2 + 20 / eps
  have hH : 2 <= H := by
    dsimp [H]
    have hp : 0 < (20 : Real) / eps := div_pos (by norm_num) hE
    linarith
  have hH0 : 0 < H := by linarith
  have hHp : 0 < H ^ 2 := by positivity
  have hEq : eps * H = 2 * eps + 20 := by dsimp [H]; field_simp [ne_of_gt hE]
  have hA : 20 <= eps * H := by rw [hEq]; linarith
  have hm := mul_le_mul_of_nonneg_left hH (mul_nonneg hE.le hH0.le)
  have hBig : 18 < eps * H ^ 2 := by nlinarith
  have hV : (18 / H ^ 2) * H ^ 2 = (18 : Real) := by field_simp [ne_of_gt hHp]
  have hFrac : 18 / H ^ 2 < eps := by
    by_contra h
    have hc : eps <= 18 / H ^ 2 := le_of_not_gt h
    have hh := mul_le_mul_of_nonneg_right hc hHp.le
    rw [hV] at hh
    linarith
  let z : Complex := Complex.mk (1 / 4) H
  have hzH : abs z.im = H := by change abs H = H; exact abs_of_nonneg hH0.le
  refine Exists.intro z (And.intro rfl (And.intro ?_ ?_))
  . rw [hzH]
    exact hH
  . have hRe : And (0 <= z.re) (z.re <= 1) := by norm_num [z]
    have hBound := cubicScalar_resonance_bound z hRe (by rw [hzH]; exact hH)
    rw [hzH] at hBound
    exact hBound.trans_lt hFrac

/-- A single cubic coordinate can cancel completely at the real central point.
This is an integer-code example, not an assertion about actual L-zero orders. -/
theorem cubicScalar_central_collision :
    integerResidueCode 3 (1 / 2 : Complex) 3 5 = 0 := by
  norm_num [integerResidueCode]

end Complex

end
