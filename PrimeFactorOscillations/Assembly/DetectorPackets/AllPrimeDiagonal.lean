/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.AllPrimeMaskFactorization

/-!
# AllPrimeDiagonal

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.AllPrimeDiagonal

def denominator (x y : Real) : Real :=
  (1 - 2 * x + x ^ 2 + y ^ 2) * (1 - (x ^ 2 + y ^ 2))

def factor (q x y : Real) : Real :=
  (1 - 2 * (q / (q - 1)) * x) / denominator x y

theorem numerator_positive (q x y : Real) (hq : 7 <= q)
    (hn : q * (x ^ 2 + y ^ 2) <= 1) :
    0 < 1 - 2 * (q / (q - 1)) * x := by
  have hq0 : 0 <= q := by linarith
  have hx : q * x ^ 2 <= 1 := by
    nlinarith [mul_nonneg hq0 (sq_nonneg y)]
  have hxq : (q * x) ^ 2 <= q := by
    have h := mul_le_mul_of_nonneg_left hx hq0
    nlinarith
  have hpoly : 0 < q ^ 2 - 6 * q + 1 := by
    nlinarith [mul_nonneg (by linarith : 0 <= q - 7)
      (by linarith : 0 <= q + 1)]
  have hgap : 0 < q - 1 - 2 * q * x := by
    by_contra h
    have hbad : q - 1 <= 2 * q * x := by linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hbad)
      (by linarith : 0 <= 2 * q * x + (q - 1))
    nlinarith
  have hd : 0 < q - 1 := by linarith
  have heq : 1 - 2 * (q / (q - 1)) * x =
      (q - 1 - 2 * q * x) / (q - 1) := by
    have hne := ne_of_gt hd
    field_simp
  rw [heq]
  exact div_pos hgap hd

theorem denominator_positive (q x y : Real) (hq : 7 <= q)
    (hn : q * (x ^ 2 + y ^ 2) <= 1) : 0 < denominator x y := by
  have hs : 0 <= x ^ 2 + y ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hseven : 7 * (x ^ 2 + y ^ 2) <= 1 :=
    (mul_le_mul_of_nonneg_right hq hs).trans hn
  have hx : x < 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  have hfirst : 0 < 1 - 2 * x + x ^ 2 + y ^ 2 := by
    have hsq := sq_pos_of_pos (sub_pos.mpr hx)
    nlinarith [sq_nonneg y]
  have hsecond : 0 < 1 - (x ^ 2 + y ^ 2) := by linarith
  exact mul_pos hfirst hsecond

theorem factor_positive (q x y : Real) (hq : 7 <= q)
    (hn : q * (x ^ 2 + y ^ 2) <= 1) : 0 < factor q x y := by
  exact div_pos (numerator_positive q x y hq hn)
    (denominator_positive q x y hq hn)

theorem exact_defect (q x y : Real) (hq : 7 <= q)
    (hn : q * (x ^ 2 + y ^ 2) <= 1) :
    factor q x y - 1 =
      ((x ^ 2 + y ^ 2) ^ 2 -
        2 * x * (x ^ 2 + y ^ 2 + 1 / (q - 1))) /
          denominator x y := by
  have hd := ne_of_gt (denominator_positive q x y hq hn)
  have hq1 : Not (q - 1 = 0) := by linarith
  unfold factor
  field_simp
  unfold denominator
  ring

theorem finite_product_positive (G : Finset Nat) (x y : Nat -> Real)
    (hq : forall p, Membership.mem G p -> 7 <= p)
    (hn : forall p, Membership.mem G p ->
      (p : Real) * ((x p) ^ 2 + (y p) ^ 2) <= 1) :
    0 < G.prod (fun p => factor (p : Real) (x p) (y p)) := by
  apply Finset.prod_pos
  intro p hp
  exact factor_positive (p : Real) (x p) (y p)
    (by exact_mod_cast hq p hp) (hn p hp)

theorem critical_defect_bound (q x y t : Real) (hq : 7 <= q)
    (hn : q * (x ^ 2 + y ^ 2) <= 1)
    (ht0 : 0 <= t) (hqt : q * t ^ 2 = 1) :
    abs (factor q x y - 1) <= 16 * t ^ 3 := by
  have hqpos : 0 < q := by linarith
  have hv0 : 0 <= x ^ 2 + y ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hvt : x ^ 2 + y ^ 2 <= t ^ 2 := by
    apply le_of_mul_le_mul_left (show q * (x ^ 2 + y ^ 2) <= q * t ^ 2 by
      rw [hqt]
      exact hn) hqpos
  have ht7 : t ^ 2 <= 1 / 7 := by
    have hb := mul_le_mul_of_nonneg_right hq (sq_nonneg t)
    rw [hqt] at hb
    linarith
  have ht : t <= 2 / 5 := by nlinarith [sq_nonneg (t - 2 / 5)]
  have hxabs : abs x <= t := by
    have hs : x ^ 2 <= t ^ 2 := by nlinarith [sq_nonneg y]
    have hb := (sq_le_sq).mp hs
    simpa only [abs_of_nonneg ht0] using hb
  have hx : x <= 2 / 5 := (le_abs_self x).trans (hxabs.trans ht)
  have hfirst : 9 / 25 <= 1 - 2 * x + x ^ 2 + y ^ 2 := by
    have hb := mul_self_le_mul_self (by norm_num : (0 : Real) <= 3 / 5)
      (by linarith : (3 : Real) / 5 <= 1 - x)
    nlinarith [sq_nonneg y]
  have hsecond : 6 / 7 <= 1 - (x ^ 2 + y ^ 2) := by linarith
  have hD : 54 / 175 <= denominator x y := by
    have hb := mul_le_mul hfirst hsecond (by norm_num)
      (by linarith : (0 : Real) <= 1 - 2 * x + x ^ 2 + y ^ 2)
    unfold denominator
    norm_num at hb
    exact hb
  have hden : 0 < q - 1 := by linarith
  have hinv0 : 0 <= 1 / (q - 1) := by positivity
  have hinv : 1 / (q - 1) <= 1 / 6 :=
    one_div_le_one_div_of_le (by norm_num : (0 : Real) < 6) (by linarith)
  have hquot : q / (q - 1) <= 7 / 6 := by
    have he : q / (q - 1) = 1 + 1 / (q - 1) := by
      have hne := ne_of_gt hden
      field_simp
      ring
    rw [he]
    linarith
  have hinvt : 1 / (q - 1) <= (7 / 6) * t ^ 2 := by
    have he : 1 / (q - 1) = (q / (q - 1)) * t ^ 2 := by
      have hne := ne_of_gt hden
      field_simp
      nlinarith [hqt]
    rw [he]
    exact mul_le_mul_of_nonneg_right hquot (sq_nonneg t)
  have ht3 : 0 <= t ^ 3 := pow_nonneg ht0 _
  have hfour : (x ^ 2 + y ^ 2) ^ 2 <= (2 / 5) * t ^ 3 := by
    have hb := mul_self_le_mul_self hv0 hvt
    have hc := mul_le_mul_of_nonneg_right ht ht3
    nlinarith
  have hplus : x ^ 2 + y ^ 2 + 1 / (q - 1) <= (13 / 6) * t ^ 2 := by
    linarith
  have hplus0 : 0 <= x ^ 2 + y ^ 2 + 1 / (q - 1) := add_nonneg hv0 hinv0
  have hcross : abs (2 * x * (x ^ 2 + y ^ 2 + 1 / (q - 1))) <=
      (13 / 3) * t ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2),
      abs_of_nonneg hplus0]
    calc
      _ <= (2 * t) * ((13 / 6) * t ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hxabs (by norm_num))
          hplus hplus0 (by positivity)
      _ = _ := by ring
  have hnum : abs ((x ^ 2 + y ^ 2) ^ 2 -
      2 * x * (x ^ 2 + y ^ 2 + 1 / (q - 1))) <=
      (71 / 15) * t ^ 3 := by
    calc
      _ <= abs ((x ^ 2 + y ^ 2) ^ 2) +
          abs (2 * x * (x ^ 2 + y ^ 2 + 1 / (q - 1))) := abs_sub _ _
      _ <= _ := by rw [abs_of_nonneg (sq_nonneg _)]; linarith
  have hDp := denominator_positive q x y hq hn
  have heq : abs (factor q x y - 1) * denominator x y =
      abs ((x ^ 2 + y ^ 2) ^ 2 -
        2 * x * (x ^ 2 + y ^ 2 + 1 / (q - 1))) := by
    rw [exact_defect q x y hq hn, abs_div, abs_of_pos hDp]
    have hne := ne_of_gt hDp
    field_simp
  have hbound := mul_le_mul_of_nonneg_right hD (abs_nonneg (factor q x y - 1))
  nlinarith

end PrimeFactorOscillations.AllPrimeDiagonal

