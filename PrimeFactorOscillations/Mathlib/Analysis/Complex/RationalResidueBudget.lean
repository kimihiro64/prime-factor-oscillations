/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.Complex.ScalarBudgetDecode

/-!
# Rational-degree scalar residue budgets

Multiplying a degree1+k/n residue by n restores an integral level. A
one-sided defect smaller than one then allows scalar integer recovery.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Complex

def rationalPowerDegree (n k : Nat) : Real := 1 + (k : Real) / (n : Real)

def realPowerResidueCode (d : Real) (z : Complex) (a b : Int) : Complex :=
  -(a : Complex) + (d : Complex) * z / (z + (d : Complex) - 1) * (b : Complex)

def realPowerResidueDefect (d : Real) (z : Complex) : Real :=
  d - ((d : Complex) * z / (z + (d : Complex) - 1)).re

theorem rationalPowerDegree_gt_one (n k : Nat) (hn : 0 < n) (hk : 0 < k) :
    1 < rationalPowerDegree n k := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hkR : (0 : Real) < k := by exact_mod_cast hk
  have h := div_pos hkR hnR
  dsimp only [rationalPowerDegree]
  linarith

theorem rationalPowerDegree_mul_den (n k : Nat) (hn : 0 < n) :
    (n : Real) * rationalPowerDegree n k = (n + k : Nat) := by
  have hnR : Not ((n : Real) = 0) := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [rationalPowerDegree, Nat.cast_add]
  field_simp

theorem realPowerResidueDefect_formula (d : Real) (hd : 1 < d)
    (z : Complex) (hRe : 0 <= z.re) :
    realPowerResidueDefect d z =
      d * (d - 1) * (z.re + d - 1) / ((z.re + d - 1) ^ 2 + z.im ^ 2) := by
  have hDen : Not (z + (d : Complex) - 1 = 0) := by
    intro h
    have hh := congrArg Complex.re h
    change z.re + d - 1 = 0 at hh
    linarith
  have he : (d : Complex) * z / (z + (d : Complex) - 1) =
      (d : Complex) - (d : Complex) * ((d : Complex) - 1) /
        (z + (d : Complex) - 1) := by
    field_simp [hDen]
    ring
  unfold realPowerResidueDefect
  rw [he]
  norm_num [Complex.div_re, Complex.normSq_apply]
  ring

theorem realPowerResidueDefect_pos (d : Real) (hd : 1 < d)
    (z : Complex) (hRe : 0 <= z.re) : 0 < realPowerResidueDefect d z := by
  have hd0 : 0 < d := by linarith
  have hd1 : 0 < d - 1 := by linarith
  have hx : 0 < z.re + d - 1 := by linarith
  rw [realPowerResidueDefect_formula d hd z hRe]
  apply div_pos (mul_pos (mul_pos hd0 hd1) hx)
  nlinarith only [sq_pos_of_pos hx, sq_nonneg z.im]

theorem realPowerResidueDefect_reference_identity (d : Real) (hd : 1 < d)
    (z : Complex) (hRe : 0 <= z.re) :
    realPowerResidueDefect d z =
      (d - 1) * (Inv.inv ((z + (d : Complex) - 1) / (d : Complex))).re := by
  have hdC : Not ((d : Complex) = 0) := by
    intro h
    have hh := congrArg Complex.re h
    change d = 0 at hh
    linarith
  have hDen : Not (z + (d : Complex) - 1 = 0) := by
    intro h
    have hh := congrArg Complex.re h
    change z.re + d - 1 = 0 at hh
    linarith
  have he : (d : Complex) * z / (z + (d : Complex) - 1) =
      (d : Complex) - ((d : Complex) - 1) *
        Inv.inv ((z + (d : Complex) - 1) / (d : Complex)) := by
    field_simp
    ring
  unfold realPowerResidueDefect
  rw [he]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.sub_im, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

theorem realPowerResidueCode_real_decomposition (d : Real) (z : Complex) (a b : Int) :
    (realPowerResidueCode d z a b).re =
      d * (b : Real) - (a : Real) - realPowerResidueDefect d z * (b : Real) := by
  simp [realPowerResidueCode, realPowerResidueDefect, Complex.mul_re]
  ring

theorem rationalPowerResidueCode_scaled_real (n k : Nat) (hn : 0 < n)
    (z : Complex) (a b : Int) :
    (n : Real) * (realPowerResidueCode (rationalPowerDegree n k) z a b).re =
      (n + k : Nat) * (b : Real) - (n : Real) * (a : Real) -
        ((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) z) * (b : Real) := by
  rw [realPowerResidueCode_real_decomposition]
  calc
    _ = ((n : Real) * rationalPowerDegree n k) * (b : Real) -
        (n : Real) * (a : Real) -
        ((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) z) * (b : Real) := by ring
    _ = _ := by rw [rationalPowerDegree_mul_den n k hn]

theorem rationalPowerResidue_zero_cost (n k : Nat) (hn : 0 < n) (hk : 0 < k)
    (z : Complex) (hRe : 0 <= z.re) (a b : Nat) (hMass : 0 < a + b)
    (hZero : (realPowerResidueCode (rationalPowerDegree n k) z (a : Int) (b : Int)).re = 0) :
    And (0 < b) (1 <= ((n : Real) *
      realPowerResidueDefect (rationalPowerDegree n k) z) * (b : Real)) := by
  have hb : 0 < b := by
    by_contra h
    have hb0 : b = 0 := by omega
    have ha0 : a = 0 := by simpa [realPowerResidueCode, hb0] using hZero
    omega
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hbR : (0 : Real) < b := by exact_mod_cast hb
  have hDelta := realPowerResidueDefect_pos _ (rationalPowerDegree_gt_one n k hn hk) z hRe
  let i : Int := ((n + k : Nat) : Int) * (b : Int) - (n : Int) * (a : Int)
  have hCast : (i : Real) = (n + k : Nat) * (b : Real) - (n : Real) * (a : Real) := by
    dsimp only [i]
    push_cast
    ring
  have hScale := rationalPowerResidueCode_scaled_real n k hn z (a : Int) (b : Int)
  rw [hZero, mul_zero] at hScale
  norm_cast at hScale
  have hi : (i : Real) = ((n : Real) *
      realPowerResidueDefect (rationalPowerDegree n k) z) * (b : Real) := by
    push_cast at hScale hCast
    linarith only [hScale, hCast]
  have hiPos : (0 : Real) < i := by rw [hi]; exact mul_pos (mul_pos hnR hDelta) hbR
  have hiInt : (0 : Int) < i := by exact_mod_cast hiPos
  have hiOne : (1 : Int) <= i := by omega
  have hiReal : (1 : Real) <= i := by exact_mod_cast hiOne
  rw [hi] at hiReal
  exact And.intro hb hiReal

def rationalPowerDecode (n k : Nat) (c delta y : Real) : Prod Int Int :=
  let ab := Real.scalarBudgetDecode (n + k) c ((n : Real) * delta) ((n : Real) * y)
  Prod.mk (ab.1 / (n : Int)) ab.2

theorem rationalPowerDecode_eq (n k : Nat) (hn : 0 < n) (hk : 0 < k)
    (z : Complex) (hRe : 0 <= z.re) (a b : Int) (c y : Real)
    (hMass : And (0 <= ((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) z) * (b : Real))
      (((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) z) * (b : Real) <= c))
    (hNoise : abs ((n : Real) * ((realPowerResidueCode (rationalPowerDegree n k) z a b).re - y)) <
      (1 - c) / 2)
    (hFine : abs ((n : Real) * ((realPowerResidueCode (rationalPowerDegree n k) z a b).re - y)) <
      ((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) z) / 2) :
    rationalPowerDecode n k c (realPowerResidueDefect (rationalPowerDegree n k) z) y =
      Prod.mk a b := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hnI : Not ((n : Int) = 0) := by exact_mod_cast (Nat.ne_of_gt hn)
  have hDelta := realPowerResidueDefect_pos _ (rationalPowerDegree_gt_one n k hn hk) z hRe
  have hScale := rationalPowerResidueCode_scaled_real n k hn z a b
  have hEq : (n + k : Nat) * (b : Real) - (((n : Int) * a : Int) : Real) -
      ((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) z) * (b : Real) -
        (n : Real) * y =
      (n : Real) * ((realPowerResidueCode (rationalPowerDegree n k) z a b).re - y) := by
    push_cast at hScale
    push_cast
    nlinarith only [hScale]
  have hDec := Real.scalarBudgetDecode_eq (n + k) ((n : Int) * a) b c
    ((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) z) ((n : Real) * y)
    (mul_pos hnR hDelta) hMass (by rw [hEq]; exact hNoise) (by rw [hEq]; exact hFine)
  rw [rationalPowerDecode, hDec]
  simp only [Int.mul_ediv_cancel_left a hnI]

end Complex
