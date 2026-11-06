/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueStrip

/-!
# The exact minimum degree for optimal residue precision

One disk test at ceil(sqrt(height)) determines the minimum degree.
Every feasible degree is at least this selected value, and every larger
one is feasible. Both integer multiplicity coordinates remain unrestricted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

def unitResidueDegreeBase (z : Complex) : Nat :=
  Nat.ceil (Real.sqrt (abs z.im))

def optimalUnitResidueDegree (z : Complex) : Nat :=
  let n := unitResidueDegreeBase z
  if norm (z + (n : Complex) - 1) <= (n : Real) * ((n : Real) - 1)
    then n else n + 1

theorem unitResidueDegreeBase_height (z : Complex) :
    Real.sqrt (abs z.im) <= (unitResidueDegreeBase z : Real) := Nat.le_ceil _

theorem unitResidueDegreeBase_square (z : Complex) :
    abs z.im <= (unitResidueDegreeBase z : Real) ^ 2 := by
  have hs := Real.sq_sqrt (abs_nonneg z.im)
  have hn := unitResidueDegreeBase_height z
  have h0 := Real.sqrt_nonneg (abs z.im)
  have hn0 : (0 : Real) <= unitResidueDegreeBase z := by positivity
  have hm := mul_nonneg (sub_nonneg.mpr hn) (add_nonneg hn0 h0)
  nlinarith only [hm, hs]

theorem unitResidueDegreeBase_ge_two (z : Complex) (hH : 2 <= abs z.im) :
    2 <= unitResidueDegreeBase z := by
  by_contra h
  have hn : unitResidueDegreeBase z <= 1 := by omega
  have hnR : (unitResidueDegreeBase z : Real) <= 1 := by exact_mod_cast hn
  have hn0 : (0 : Real) <= unitResidueDegreeBase z := by positivity
  have hs := unitResidueDegreeBase_square z
  nlinarith only [hnR, hn0, hs, hH]

theorem integerResidueCode_disk_mono (d e : Nat) (hd : 2 <= d) (hde : d <= e)
    (z : Complex)
    (hDisk : norm (z + (d : Complex) - 1) <= (d : Real) * ((d : Real) - 1)) :
    norm (z + (e : Complex) - 1) <= (e : Real) * ((e : Real) - 1) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hdeR : (d : Real) <= e := by exact_mod_cast hde
  have hc : (e : Complex) - (d : Complex) =
      (((e : Real) - (d : Real) : Real) : Complex) := by
    apply Complex.ext <;> simp
  have hNorm : norm ((e : Complex) - (d : Complex)) = (e : Real) - (d : Real) := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hdeR)]
  have he : z + (e : Complex) - 1 =
      (z + (d : Complex) - 1) + ((e : Complex) - (d : Complex)) := by ring
  have hTri := norm_add_le (z + (d : Complex) - 1) ((e : Complex) - (d : Complex))
  rw [<- he, hNorm] at hTri
  have hp := mul_nonneg (sub_nonneg.mpr hdeR)
    (by linarith : 0 <= (e : Real) + (d : Real) - 2)
  nlinarith only [hDisk, hTri, hp]

theorem unitResidueDegreeBase_successor_disk (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im) :
    norm (z + ((unitResidueDegreeBase z + 1 : Nat) : Complex) - 1) <=
      ((unitResidueDegreeBase z + 1 : Nat) : Real) *
        (((unitResidueDegreeBase z + 1 : Nat) : Real) - 1) := by
  let n := unitResidueDegreeBase z
  let r := (n : Real)
  let H := abs z.im
  have hn : 2 <= n := unitResidueDegreeBase_ge_two z hH
  have hr : (2 : Real) <= r := by
    change (2 : Real) <= (n : Real)
    exact_mod_cast hn
  have hr0 : 0 <= r := by positivity
  have hH0 : 0 <= H := abs_nonneg _
  have hHs : H ^ 2 = z.im ^ 2 := sq_abs _
  have hSq : H <= r ^ 2 := unitResidueDegreeBase_square z
  have hm := mul_nonneg (sub_nonneg.mpr hSq) (add_nonneg (sq_nonneg r) hH0)
  have hFourth : H ^ 2 <= r ^ 4 := by nlinarith only [hm]
  have hrSq : 4 <= r ^ 2 := by nlinarith only [hr]
  have hMul := mul_le_mul_of_nonneg_right hrSq hr0
  have hCube : 4 * r <= r ^ 3 := by nlinarith only [hMul]
  have hMargin : r ^ 4 + (r + 1) ^ 2 <= (r * (r + 1)) ^ 2 := by
    nlinarith only [hCube, hr]
  have hx0 : 0 <= z.re + r := by linarith [hRe.1]
  have hx1 : z.re + r <= r + 1 := by linarith [hRe.2]
  have hxSq : (z.re + r) ^ 2 <= (r + 1) ^ 2 := by nlinarith only [hx0, hx1, hr]
  have hDsq : norm (z + (n : Complex)) ^ 2 = (z.re + r) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [r]
    ring
  have hD : norm (z + (n : Complex)) <= r * (r + 1) := by
    have hN0 := norm_nonneg (z + (n : Complex))
    have hp0 : 0 <= r * (r + 1) := mul_nonneg hr0 (by linarith)
    nlinarith only [hDsq, hFourth, hMargin, hxSq, hHs, hN0, hp0]
  have he : z + ((n + 1 : Nat) : Complex) - 1 = z + (n : Complex) := by
    push_cast
    ring
  change norm (z + ((n + 1 : Nat) : Complex) - 1) <=
    ((n + 1 : Nat) : Real) * (((n + 1 : Nat) : Real) - 1)
  rw [he]
  push_cast
  dsimp [r] at hD
  nlinarith only [hD]

theorem optimalUnitResidueDegree_ge_base (z : Complex) :
    unitResidueDegreeBase z <= optimalUnitResidueDegree z := by
  dsimp [optimalUnitResidueDegree]
  split <;> omega

theorem optimalUnitResidueDegree_le_successor (z : Complex) :
    optimalUnitResidueDegree z <= unitResidueDegreeBase z + 1 := by
  dsimp [optimalUnitResidueDegree]
  split <;> omega

theorem optimalUnitResidueDegree_ge_two (z : Complex) (hH : 2 <= abs z.im) :
    2 <= optimalUnitResidueDegree z :=
  (unitResidueDegreeBase_ge_two z hH).trans (optimalUnitResidueDegree_ge_base z)

theorem optimalUnitResidueDegree_disk (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im) :
    norm (z + (optimalUnitResidueDegree z : Complex) - 1) <=
      (optimalUnitResidueDegree z : Real) * ((optimalUnitResidueDegree z : Real) - 1) := by
  dsimp [optimalUnitResidueDegree]
  split
  . assumption
  . exact unitResidueDegreeBase_successor_disk z hRe hH

theorem integerResidueCode_disk_height_lt (d : Nat) (hd : 2 <= d) (z : Complex)
    (hDisk : norm (z + (d : Complex) - 1) <= (d : Real) * ((d : Real) - 1)) :
    Real.sqrt (abs z.im) < (d : Real) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hHD : abs z.im <= norm (z + (d : Complex) - 1) := by
    simpa using Complex.abs_im_le_norm (z + (d : Complex) - 1)
  have hs := Real.sq_sqrt (abs_nonneg z.im)
  have h0 := Real.sqrt_nonneg (abs z.im)
  by_contra h
  have hSD : (d : Real) <= Real.sqrt (abs z.im) := le_of_not_gt h
  have hm := mul_nonneg (sub_nonneg.mpr hSD)
    (by linarith : 0 <= Real.sqrt (abs z.im) + (d : Real))
  nlinarith only [hm, hs, hHD, hDisk, hdR]

theorem unitResidueDegreeBase_le_of_disk (d : Nat) (hd : 2 <= d) (z : Complex)
    (hDisk : norm (z + (d : Complex) - 1) <= (d : Real) * ((d : Real) - 1)) :
    unitResidueDegreeBase z <= d := by
  exact Nat.ceil_le.mpr (integerResidueCode_disk_height_lt d hd z hDisk).le

theorem optimalUnitResidueDegree_minimal (d : Nat) (hd : 2 <= d) (z : Complex)
    (hDisk : norm (z + (d : Complex) - 1) <= (d : Real) * ((d : Real) - 1)) :
    optimalUnitResidueDegree z <= d := by
  have hn := unitResidueDegreeBase_le_of_disk d hd z hDisk
  by_cases hBase : norm (z + (unitResidueDegreeBase z : Complex) - 1) <=
      (unitResidueDegreeBase z : Real) * ((unitResidueDegreeBase z : Real) - 1)
  . simpa only [optimalUnitResidueDegree, ite_eq_left hBase] using hn
  . have hNe : Not (d = unitResidueDegreeBase z) := by
      intro he
      subst d
      exact hBase hDisk
    have hLt : unitResidueDegreeBase z + 1 <= d := by omega
    simpa only [optimalUnitResidueDegree, ite_eq_right hBase] using hLt

theorem integerResidueCode_optimal_degree_iff (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im) :
    (forall a b : Int, Not (And (a = 0) (b = 0)) ->
      1 <= norm (integerResidueCode d z a b)) <-> optimalUnitResidueDegree z <= d := by
  rw [integerResidueCode_strip_unit_iff d hd z hRe hH]
  constructor
  . exact optimalUnitResidueDegree_minimal d hd z
  . intro h
    exact integerResidueCode_disk_mono (optimalUnitResidueDegree z) d
      (optimalUnitResidueDegree_ge_two z hH) h z (optimalUnitResidueDegree_disk z hRe hH)

theorem optimalUnitResidueDegree_height_bounds (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im) :
    And (Real.sqrt (abs z.im) < (optimalUnitResidueDegree z : Real))
      ((optimalUnitResidueDegree z : Real) < Real.sqrt (abs z.im) + 2) := by
  refine And.intro ?_ ?_
  . exact integerResidueCode_disk_height_lt (optimalUnitResidueDegree z)
      (optimalUnitResidueDegree_ge_two z hH) z (optimalUnitResidueDegree_disk z hRe hH)
  . have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (abs z.im))
    have hu : (optimalUnitResidueDegree z : Real) <= (unitResidueDegreeBase z : Real) + 1 := by
      exact_mod_cast optimalUnitResidueDegree_le_successor z
    change (unitResidueDegreeBase z : Real) < Real.sqrt (abs z.im) + 1 at hc
    linarith

theorem integerResidueCode_optimal_spacing (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im) :
    min 1 ((optimalUnitResidueDegree z : Real) * ((optimalUnitResidueDegree z : Real) - 1) /
      norm (z + (optimalUnitResidueDegree z : Complex) - 1)) = 1 := by
  let d := optimalUnitResidueDegree z
  have hDisk := optimalUnitResidueDegree_disk z hRe hH
  have hHD : abs z.im <= norm (z + (d : Complex) - 1) := by
    simpa using Complex.abs_im_le_norm (z + (d : Complex) - 1)
  have hD : 0 < norm (z + (d : Complex) - 1) := by linarith
  have he : (((d : Real) * ((d : Real) - 1)) / norm (z + (d : Complex) - 1)) *
      norm (z + (d : Complex) - 1) = (d : Real) * ((d : Real) - 1) := by field_simp
  have hRatio : 1 <= ((d : Real) * ((d : Real) - 1)) / norm (z + (d : Complex) - 1) :=
    le_of_mul_le_mul_right (by rw [one_mul, he]; exact hDisk) hD
  exact min_eq_left hRatio

end Complex

end
