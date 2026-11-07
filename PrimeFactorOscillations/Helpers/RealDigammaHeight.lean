/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-!
# A unit leading coefficient in the digamma height bound

The harmonic head is retained before taking norms. Its inverse-resolvent
correction and the complete shifted tail are bounded independently of height.
This keeps coefficient one on the logarithm.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Complex
open scoped BigOperators

theorem digamma_re_height_upper (z : Complex) (b : Real)
    (hz : 1 <= z.re) (hb : z.re <= b) (ht : 1 <= abs z.im) :
    (digamma z).re <= Real.log (abs z.im) +
      (b + 6 + Real.log 3 + abs Real.eulerMascheroniConstant) := by
  have hre : 0 < z.re := by linarith only [hz]
  have htpos : 0 < abs z.im := by linarith only [ht]
  have hbpos : 0 < b := hre.trans_le hb
  let N : Nat := Nat.ceil (abs z.im) + 1
  have hN1 : 1 <= N := Nat.le_add_left 1 _
  have hN1R : (1 : Real) <= (N : Real) := by exact_mod_cast hN1
  have hNpos : (0 : Real) < N := by linarith only [hN1R]
  have hNim : abs z.im <= (N : Real) := by
    dsimp only [N]
    push_cast
    have h := Nat.le_ceil (abs z.im)
    linarith only [h]
  have hNle : (N : Real) <= abs z.im + 2 := by
    dsimp only [N]
    push_cast
    have h := Nat.ceil_lt_add_one (abs_nonneg z.im)
    linarith only [h]
  have hNthree : (N : Real) <= 3 * abs z.im := by
    linarith only [hNle, ht]
  have hsum := hasSum_digamma_of_re_pos hre
  have hmaj : Summable (fun n : Nat =>
      (norm z + 1) / (((n : Real) + 1) ^ 2)) := by
    refine (summable_one_div_natCast_add_one_sq.mul_left (norm z + 1)).congr
      (fun n => ?_)
    rw [mul_one_div]
  have hnormsum : Summable (fun n : Nat =>
      norm (((n : Complex) + 1) ^ (-1 : Int) -
        (z + (n : Complex)) ^ (-1 : Int))) := by
    simp only [zpow_neg_one]
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hmaj
    simpa only [one_mul] using
      norm_inv_add_one_sub_inv_le (by norm_num : (0 : Real) < 1)
        (by norm_num : (1 : Real) <= 1) hz (le_refl (norm z)) n
  have hhead : norm (Finset.sum (Finset.range N)
      (fun n : Nat => (z + (n : Complex)) ^ (-1 : Int))) <= 3 := by
    calc
      norm (Finset.sum (Finset.range N)
          (fun n : Nat => (z + (n : Complex)) ^ (-1 : Int))) <=
          Finset.sum (Finset.range N)
            (fun n : Nat => norm ((z + (n : Complex)) ^ (-1 : Int))) :=
        norm_sum_le _ _
      _ <= Finset.sum (Finset.range N)
          (fun _ : Nat => 1 / abs z.im) := by
        apply Finset.sum_le_sum
        intro n _
        rw [zpow_neg_one, norm_inv, <- one_div]
        apply one_div_le_one_div_of_le htpos
        simpa using Complex.abs_im_le_norm (z + (n : Complex))
      _ = (N : Real) / abs z.im := by simp [div_eq_mul_inv]
      _ <= 3 := by
        have h := div_le_div_of_nonneg_right hNthree htpos.le
        simpa [ne_of_gt htpos] using h
  have hshiftNorm := (summable_nat_add_iff N).mpr hnormsum
  have hshiftMaj := (summable_nat_add_iff N).mpr hmaj
  have hzNorm : norm z <= b + abs z.im := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hre] at h
    linarith only [h, hb]
  have hNkey : norm z + 1 <= (b + 2) * (N : Real) := by
    have h := mul_le_mul_of_nonneg_left hN1R hbpos.le
    nlinarith only [h, hzNorm, hNim, hN1R]
  have htail : norm (tsum (fun i : Nat =>
      ((((i + N : Nat) : Complex) + 1) ^ (-1 : Int) -
        (z + ((i + N : Nat) : Complex)) ^ (-1 : Int)))) <= b + 2 := by
    calc
      norm (tsum (fun i : Nat =>
          ((((i + N : Nat) : Complex) + 1) ^ (-1 : Int) -
            (z + ((i + N : Nat) : Complex)) ^ (-1 : Int)))) <=
          tsum (fun i : Nat => norm
            ((((i + N : Nat) : Complex) + 1) ^ (-1 : Int) -
              (z + ((i + N : Nat) : Complex)) ^ (-1 : Int))) :=
        norm_tsum_le_tsum_norm hshiftNorm
      _ <= tsum (fun i : Nat =>
          (norm z + 1) / ((((i + N : Nat) : Real) + 1) ^ 2)) := by
        apply hshiftNorm.tsum_le_tsum _ hshiftMaj
        intro i
        simpa only [zpow_neg_one, one_mul] using
          norm_inv_add_one_sub_inv_le (by norm_num : (0 : Real) < 1)
            (by norm_num : (1 : Real) <= 1) hz (le_refl (norm z)) (i + N)
      _ = (norm z + 1) * tsum (fun i : Nat =>
          1 / ((((i + N : Nat) : Real) + 1) ^ 2)) := by
        rw [<- tsum_mul_left]
        apply tsum_congr
        intro i
        rw [mul_one_div]
      _ <= (norm z + 1) * Inv.inv (N : Real) :=
        mul_le_mul_of_nonneg_left
          (tsum_one_div_natCast_add_add_one_sq_le hN1) (by positivity)
      _ <= b + 2 := by
        have h := div_le_div_of_nonneg_right hNkey hNpos.le
        simpa [div_eq_mul_inv, ne_of_gt hNpos] using h
  have hH : ((harmonic N : Rat) : Real) <=
      Real.log (abs z.im) + 1 + Real.log 3 := by
    calc
      ((harmonic N : Rat) : Real) <= 1 + Real.log (N : Real) :=
        harmonic_le_one_add_log N
      _ <= 1 + Real.log (3 * abs z.im) :=
        by
          have h := Real.log_le_log hNpos hNthree
          linarith only [h]
      _ = _ := by
        rw [Real.log_mul (by norm_num : Not ((3 : Real) = 0)) (ne_of_gt htpos)]
        ring
  have hsplit :
      (Finset.sum (Finset.range N) (fun n : Nat =>
        ((n : Complex) + 1) ^ (-1 : Int) -
          (z + (n : Complex)) ^ (-1 : Int))) +
      tsum (fun i : Nat =>
        (((i + N : Nat) : Complex) + 1) ^ (-1 : Int) -
          (z + ((i + N : Nat) : Complex)) ^ (-1 : Int)) =
      digamma z + Real.eulerMascheroniConstant := by
    simp only [zpow_neg_one]
    exact (hsum.summable.sum_add_tsum_nat_add N).trans hsum.tsum_eq
  rw [Finset.sum_sub_distrib] at hsplit
  have hHarmonic : Finset.sum (Finset.range N)
      (fun n : Nat => ((n : Complex) + 1) ^ (-1 : Int)) =
      ((harmonic N : Rat) : Complex) := by
    simpa only [zpow_neg_one] using sum_inv_natCast_add_one N
  rw [hHarmonic] at hsplit
  have hReal := congrArg Complex.re hsplit
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ratCast_re] at hReal
  have hh := (neg_le_abs
      ((Finset.sum (Finset.range N)
        (fun n : Nat => (z + (n : Complex)) ^ (-1 : Int))).re)).trans
    (Complex.abs_re_le_norm _)
  have htReal := (Complex.re_le_norm
      (tsum (fun i : Nat =>
        (((i + N : Nat) : Complex) + 1) ^ (-1 : Int) -
          (z + ((i + N : Nat) : Complex)) ^ (-1 : Int)))).trans htail
  have hEuler := neg_le_abs Real.eulerMascheroniConstant
  linarith only [hReal, hH, hh, htReal, hhead, hEuler]

theorem digamma_lipschitz_right (z w : Complex)
    (hz : 1 <= z.re) (hw : 1 <= w.re) :
    norm (digamma z - digamma w) <= norm (z - w) *
      tsum (fun n : Nat => 1 / (((n : Real) + 1) ^ 2)) := by
  let a : Nat -> Complex := fun n =>
    (Inv.inv ((n : Complex) + 1) - Inv.inv (z + (n : Complex))) -
      (Inv.inv ((n : Complex) + 1) - Inv.inv (w + (n : Complex)))
  have hBound (n : Nat) : norm (a n) <=
      norm (z - w) / (((n : Real) + 1) ^ 2) := by
    have hn : 0 < (n : Real) + 1 := by positivity
    have hZ : (n : Real) + 1 <= norm (z + (n : Complex)) := by
      have hh := Complex.re_le_norm (z + (n : Complex))
      simp only [Complex.add_re, Complex.natCast_re] at hh
      linarith only [hz, hh]
    have hW : (n : Real) + 1 <= norm (w + (n : Complex)) := by
      have hh := Complex.re_le_norm (w + (n : Complex))
      simp only [Complex.add_re, Complex.natCast_re] at hh
      linarith only [hw, hh]
    have hz0 : Not (z + (n : Complex) = 0) :=
      norm_pos_iff.mp (hn.trans_le hZ)
    have hw0 : Not (w + (n : Complex) = 0) :=
      norm_pos_iff.mp (hn.trans_le hW)
    have hAtom : a n =
        (z - w) / ((w + (n : Complex)) * (z + (n : Complex))) := by
      dsimp only [a]
      field_simp [hz0, hw0]
      ring
    rw [hAtom, norm_div, norm_mul]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hn)
    have hh := mul_le_mul hW hZ hn.le (norm_nonneg _)
    nlinarith only [hh]
  have hMaj : Summable (fun n : Nat =>
      norm (z - w) / (((n : Real) + 1) ^ 2)) := by
    refine (summable_one_div_natCast_add_one_sq.mul_left (norm (z - w))).congr
      (fun n => ?_)
    rw [mul_one_div]
  have hNorm : Summable (fun n : Nat => norm (a n)) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hBound hMaj
  have hs : HasSum a (digamma z - digamma w) := by
    have h := (hasSum_digamma_of_re_pos
      (show 0 < z.re by linarith only [hz])).sub
        (hasSum_digamma_of_re_pos (show 0 < w.re by linarith only [hw]))
    convert h using 1 <;> ring
  rw [<- hs.tsum_eq]
  calc
    norm (tsum a) <= tsum (fun n : Nat => norm (a n)) :=
      norm_tsum_le_tsum_norm hNorm
    _ <= tsum (fun n : Nat => norm (z - w) / (((n : Real) + 1) ^ 2)) :=
      hNorm.tsum_le_tsum hBound hMaj
    _ = _ := by
      rw [<- tsum_mul_left]
      apply tsum_congr
      intro n
      rw [mul_one_div]

end PrimeFactorOscillations
