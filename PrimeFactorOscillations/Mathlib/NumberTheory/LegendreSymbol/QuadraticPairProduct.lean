/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwists

/-!
# Uniform finite Euler-product tails

A summable inverse-square local defect gives an explicit logarithmic
comparison for every finite supported tail. The proof keeps the actual
factor product and uses its positivity before taking logarithms.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open scoped BigOperators

namespace FiniteField.QuadraticPairEuler

theorem log_abs_bound (x : Real) (hx : 1 / 2 <= x) :
    |Real.log x| <= 2 * |x - 1| := by
  have hxpos : 0 < x := by linarith
  have hxne := ne_of_gt hxpos
  have he0 : 0 <= |x - 1| := abs_nonneg (x - 1)
  have hl := Real.log_le_sub_one_of_pos hxpos
  have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hxpos)
  rw [Real.log_inv] at hi
  have hInv : x ^ (-1 : Int) - 1 <= 2 * |x - 1| := by
    have hId : x ^ (-1 : Int) * x = 1 := by field_simp [hxne]
    have hOne : 1 - x <= |x - 1| := by linarith [neg_le_abs (x - 1)]
    have hScale : |x - 1| <= 2 * |x - 1| * x := by nlinarith
    by_contra hn
    have hgt : 0 < x ^ (-1 : Int) - 1 - 2 * |x - 1| := by linarith
    nlinarith [mul_pos hgt hxpos]
  apply abs_le.mpr
  constructor
  . simp only [zpow_neg_one] at hInv
    linarith only [hi, hInv]
  . linarith [le_abs_self (x - 1)]

theorem inverse_square_step (x : Real) (hx : 1 < x) :
    1 / x ^ 2 <= 1 / (x - 1) - 1 / x := by
  have hx0 : 0 < x := by linarith
  have hxne := ne_of_gt hx0
  have hxm : 0 < x - 1 := by linarith
  have hxmne := ne_of_gt hxm
  have heq : 1 / (x - 1) - 1 / x - 1 / x ^ 2 =
      1 / (x ^ 2 * (x - 1)) := by
    field_simp [hxne, hxmne]
    <;> ring
  have hpos : 0 <= (1 : Real) / (x ^ 2 * (x - 1)) := by positivity
  linarith only [heq, hpos]

theorem sum_inverse_square_tail (N M : Nat) (hN : 1 <= N) (hNM : N <= M)
    (T : Finset Nat) (hT : T <= Finset.Ico (N + 1) (M + 1)) :
    T.sum (fun n => (1 : Real) / (n : Real) ^ 2) <= 1 / (N : Real) := by
  have hmass :
      T.sum (fun n => (1 : Real) / (n : Real) ^ 2) <=
        (Finset.Ico (N + 1) (M + 1)).sum (fun n => (1 : Real) / (n : Real) ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun n _ _ => by positivity)
  let f : Nat -> Real := fun n => -1 / ((n : Real) - 1)
  have hstep (n : Nat) :
      (1 : Real) / ((n : Real) - 1) - 1 / (n : Real) = f (n + 1) - f n := by
    simp only [f, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    ring
  calc
    _ <= (Finset.Ico (N + 1) (M + 1)).sum (fun n => (1 : Real) / (n : Real) ^ 2) := hmass
    _ <= (Finset.Ico (N + 1) (M + 1)).sum
        (fun n => (1 : Real) / ((n : Real) - 1) - 1 / (n : Real)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnN : N < n := Nat.lt_of_succ_le (Finset.mem_Ico.mp hn).1
      have hn1 : 1 < n := lt_of_le_of_lt hN hnN
      have hnR : (1 : Real) < (n : Real) := by exact_mod_cast hn1
      exact inverse_square_step n hnR
    _ = (Finset.Ico (N + 1) (M + 1)).sum (fun n => f (n + 1) - f n) :=
      Finset.sum_congr rfl (fun n _ => hstep n)
    _ = f (M + 1) - f (N + 1) :=
      Finset.sum_Ico_sub f (Nat.add_le_add_right hNM 1)
    _ = (1 : Real) / (N : Real) - 1 / (M : Real) := by
      simp only [f, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      ring
    _ <= 1 / (N : Real) := by
      have hm0 : 0 <= (1 : Real) / (M : Real) := by positivity
      linarith

theorem log_product_tail_bound (N M : Nat) (hN : 1 <= N) (hNM : N <= M)
    (T : Finset Nat) (hT : T <= Finset.Ico (N + 1) (M + 1))
    (g : Nat -> Real) (C : Real) (hC : 0 <= C)
    (hb : forall n, Membership.mem T n -> |g n - 1| <= C / (n : Real) ^ 2)
    (hs : forall n, Membership.mem T n -> C / (n : Real) ^ 2 <= 1 / 2) :
    |Real.log (T.prod g)| <= 2 * C / (N : Real) := by
  have hg (n : Nat) (hn : Membership.mem T n) : (1 / 2 : Real) <= g n := by
    have h := abs_le.mp ((hb n hn).trans (hs n hn))
    linarith only [h.1]
  have hl (n : Nat) (hn : Membership.mem T n) :
      |Real.log (g n)| <= 2 * C / (n : Real) ^ 2 := by
    calc
      _ <= 2 * |g n - 1| := log_abs_bound (g n) (hg n hn)
      _ <= 2 * (C / (n : Real) ^ 2) :=
        mul_le_mul_of_nonneg_left (hb n hn) (by norm_num)
      _ = _ := by ring
  have hsum (r : Nat -> Real)
      (hr : forall n, Membership.mem T n -> r n <= 2 * C / (n : Real) ^ 2) :
      T.sum r <= 2 * C / (N : Real) := by
    calc
      _ <= T.sum (fun n => 2 * C / (n : Real) ^ 2) :=
        Finset.sum_le_sum (fun n hn => hr n hn)
      _ = (2 * C) * T.sum (fun n => (1 : Real) / (n : Real) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ <= (2 * C) * (1 / (N : Real)) :=
        mul_le_mul_of_nonneg_left (sum_inverse_square_tail N M hN hNM T hT) (by positivity)
      _ = _ := by ring
  have hHi := hsum (fun n => Real.log (g n))
    (fun n hn => (le_abs_self _).trans (hl n hn))
  have hLo := hsum (fun n => -Real.log (g n))
    (fun n hn => (neg_le_abs _).trans (hl n hn))
  rw [Finset.sum_neg_distrib] at hLo
  rw [Real.log_prod (fun n hn => ne_of_gt (by linarith [hg n hn] : 0 < g n))]
  exact abs_le.mpr (And.intro (by linarith only [hLo]) hHi)

theorem corrected_product_log_bound
    (N M : Nat) (hN : 256 <= N) (hNM : N <= M)
    (T : Finset Nat) (hT : T <= Finset.Ico (N + 1) (M + 1))
    (a e f x y : Nat -> Real)
    (ha : forall n, Membership.mem T n -> (a n) ^ 2 <= 4 * (n : Real))
    (he : forall n, Membership.mem T n -> e n = 1 \/ e n = -1)
    (hf : forall n, Membership.mem T n -> f n = 1 \/ f n = -1)
    (hx : forall n, Membership.mem T n -> x n = 1 \/ x n = -1)
    (hy : forall n, Membership.mem T n -> y n = 1 \/ y n = -1) :
    |Real.log (T.prod (fun n => correctedCarrier n (a n) (e n) (f n) (x n) (y n)))| <=
      65664 / (N : Real) := by
  let g : Nat -> Real := fun n => correctedCarrier n (a n) (e n) (f n) (x n) (y n)
  have hnLower (n : Nat) (hn : Membership.mem T n) : (257 : Real) <= (n : Real) := by
    have hnNat : 257 <= n :=
      le_trans (Nat.succ_le_succ hN) (Finset.mem_Ico.mp (hT hn)).1
    exact_mod_cast hnNat
  have hb (n : Nat) (hn : Membership.mem T n) : |g n - 1| <= 32832 / (n : Real) ^ 2 := by
    exact corrected_carrier_bound n (a n) (e n) (f n) (x n) (y n)
      (by linarith [hnLower n hn]) (ha n hn) (he n hn) (hf n hn) (hx n hn) (hy n hn)
  have hs (n : Nat) (hn : Membership.mem T n) : (32832 : Real) / (n : Real) ^ 2 <= 1 / 2 := by
    have hln := hnLower n hn
    have hn0 : (0 : Real) < (n : Real) := by linarith
    have hnne := ne_of_gt hn0
    have hsq : (65664 : Real) <= (n : Real) ^ 2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hln)
        (by linarith : 0 <= (n : Real) + 257)
      nlinarith
    calc
      (32832 : Real) / (n : Real) ^ 2 <=
          ((n : Real) ^ 2 / 2) / (n : Real) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith only [hsq]) (sq_nonneg _)
      _ = 1 / 2 := by field_simp [hnne]
  have hN1 : 1 <= N := le_trans (by norm_num : 1 <= (256 : Nat)) hN
  have h := log_product_tail_bound N M hN1 hNM T hT g 32832 (by norm_num) hb hs
  norm_num only [show (2 : Real) * 32832 = 65664 by norm_num] at h
  exact h

theorem product_bounds_of_log_bound (u B : Real) (hu : 0 < u)
    (h : |Real.log u| <= B) :
    Real.exp (-B) <= u /\ u <= Real.exp B := by
  have hb := abs_le.mp h
  constructor
  . calc
      Real.exp (-B) <= Real.exp (Real.log u) := Real.exp_le_exp.mpr hb.1
      _ = u := Real.exp_log hu
  . calc
      u = Real.exp (Real.log u) := (Real.exp_log hu).symm
      _ <= Real.exp B := Real.exp_le_exp.mpr hb.2

theorem corrected_product_bounds
    (N M : Nat) (hN : 256 <= N) (hNM : N <= M)
    (T : Finset Nat) (hT : T <= Finset.Ico (N + 1) (M + 1))
    (a e f x y : Nat -> Real)
    (ha : forall n, Membership.mem T n -> (a n) ^ 2 <= 4 * (n : Real))
    (he : forall n, Membership.mem T n -> e n = 1 \/ e n = -1)
    (hf : forall n, Membership.mem T n -> f n = 1 \/ f n = -1)
    (hx : forall n, Membership.mem T n -> x n = 1 \/ x n = -1)
    (hy : forall n, Membership.mem T n -> y n = 1 \/ y n = -1) :
    Real.exp (-65664 / (N : Real)) <=
      T.prod (fun n => correctedCarrier n (a n) (e n) (f n) (x n) (y n)) /\
        T.prod (fun n => correctedCarrier n (a n) (e n) (f n) (x n) (y n)) <=
          Real.exp (65664 / (N : Real)) := by
  have hp : 0 < T.prod (fun n => correctedCarrier n (a n) (e n) (f n) (x n) (y n)) := by
    apply Finset.prod_pos
    intro n hn
    have hnNat : 257 <= n :=
      le_trans (Nat.succ_le_succ hN) (Finset.mem_Ico.mp (hT hn)).1
    have hnR : (257 : Real) <= (n : Real) := by exact_mod_cast hnNat
    exact corrected_carrier_pos n (a n) (e n) (f n) (x n) (y n)
      (by linarith) (ha n hn) (he n hn) (hf n hn) (hx n hn) (hy n hn)
  have hl := corrected_product_log_bound N M hN hNM T hT a e f x y ha he hf hx hy
  have h := product_bounds_of_log_bound _ _ hp hl
  simpa only [neg_div] using h

end FiniteField.QuadraticPairEuler
