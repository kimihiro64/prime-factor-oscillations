/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Pow.NatSum
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.LargestPrimeFactorBounds

/-!
# Quantitative prime-prefix transfer for largest prime factors

A prime-prefix bound C * t^b on the complete interval 0 <= t <= X gives the
explicit total row bound (2*C/(1-b)) * X * y^(b-1), for 0 <= b < 1.
This yields both the smooth-number and largest-factor-twist bounds. At b=7/8
the complete coefficient is 16*C. The analytic prime-prefix hypothesis is
explicit; no unconditional prime-character estimate is claimed in this module.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem sum_prime_Icc_eq_sub (f : Nat -> Complex) (a b : Nat)
    (hab : a <= b + 1) :
    Finset.sum ((Finset.Icc a b).filter Nat.Prime) f =
      Finset.sum (primesBelow (b + 1)) f - Finset.sum (primesBelow a) f := by
  have hset : Finset.Icc a b = Finset.Ico a (b + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  rw [hset]
  simpa only [primesBelow, Finset.sum_filter] using
    Finset.sum_Ico_eq_sub (fun n => if Nat.Prime n then f n else 0) hab

theorem norm_sum_largestPrimeFactorRow_le (f : Nat -> Complex) (B : Nat -> Real)
    (X y m : Nat) (hmono : Monotone B)
    (hprefix : forall t, t <= X -> norm (Finset.sum (primesBelow (t + 1)) f) <= B t) :
    norm (Finset.sum (largestPrimeFactorRow X y m) f) <= 2 * B (X / m) := by
  let L := max (y + 1) (largestPrimeFactor m)
  let U := X / m
  have hU : U <= X := Nat.div_le_self _ _
  have hL : 1 <= L := (Nat.succ_le_succ (Nat.zero_le y)).trans (le_max_left _ _)
  have hBU : 0 <= B U := (norm_nonneg _).trans (hprefix U hU)
  by_cases hLU : L <= U
  next =>
    have hsub : L - 1 <= U := (Nat.sub_le _ _).trans hLU
    have hsum : Finset.sum (largestPrimeFactorRow X y m) f =
        Finset.sum (primesBelow (U + 1)) f - Finset.sum (primesBelow ((L - 1) + 1)) f := by
      rw [Nat.sub_add_cancel hL]
      exact sum_prime_Icc_eq_sub f L U (Nat.le_succ_of_le hLU)
    rw [hsum]
    calc
      _ <= norm (Finset.sum (primesBelow (U + 1)) f) +
          norm (Finset.sum (primesBelow ((L - 1) + 1)) f) := norm_sub_le _ _
      _ <= B U + B (L - 1) :=
        _root_.add_le_add (hprefix U hU) (hprefix _ (hsub.trans hU))
      _ <= B U + B U := _root_.add_le_add le_rfl (hmono hsub)
      _ = 2 * B U := by ring
  next =>
    have hempty : largestPrimeFactorRow X y m = {} := by
      unfold largestPrimeFactorRow
      rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hLU), Finset.filter_empty]
    rw [hempty, Finset.sum_empty, norm_zero]
    exact mul_nonneg (by norm_num) hBU


/-- A finite prime-prefix power bound controls the complete sum of row errors. -/
theorem sum_norm_largestPrimeFactor_rows_le_rpow (f : Nat -> Complex)
    (X y : Nat) (hX : 0 < X) (hy : 0 < y)
    (b C : Real) (hb0 : 0 <= b) (hb1 : b < 1) (hC : 0 <= C)
    (hprefix : forall t, t <= X ->
      norm (Finset.sum (primesBelow (t + 1)) f) <= C * (t : Real) ^ b) :
    Finset.sum (Finset.Icc 1 (X / y)) (fun m =>
      norm (Finset.sum (largestPrimeFactorRow X y m) f)) <=
      (2 * C / (1 - b)) * (X : Real) * (y : Real) ^ (b - 1) := by
  have hmono : Monotone (fun t : Nat => C * (t : Real) ^ b) := by
    intro t u htu
    exact _root_.mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg t) (Nat.cast_le.mpr htu) hb0) hC
  have hrow : forall m, Membership.mem (Finset.Icc 1 (X / y)) m ->
      norm (Finset.sum (largestPrimeFactorRow X y m) f) <=
        (2 * C) * ((X : Real) / (m : Real)) ^ b := by
    intro m hm
    have hmR : 0 < (m : Real) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hm).1
    have hraw : ((X / m : Nat) : Real) * (m : Real) <= (X : Real) := by
      exact_mod_cast Nat.div_mul_le_self X m
    have hfloor : ((X / m : Nat) : Real) <= (X : Real) / (m : Real) := by
      simpa [hmR.ne'] using _root_.div_le_div_of_nonneg_right hraw hmR.le
    calc
      _ <= 2 * (C * ((X / m : Nat) : Real) ^ b) :=
        norm_sum_largestPrimeFactorRow_le f _ X y m hmono hprefix
      _ <= 2 * (C * ((X : Real) / (m : Real)) ^ b) := by gcongr
      _ = (2 * C) * ((X : Real) / (m : Real)) ^ b := by ring
  calc
    _ <= Finset.sum (Finset.Icc 1 (X / y)) (fun m =>
        (2 * C) * ((X : Real) / (m : Real)) ^ b) := Finset.sum_le_sum hrow
    _ = (2 * C) * Finset.sum (Finset.Icc 1 (X / y))
        (fun m => ((X : Real) / (m : Real)) ^ b) := (Finset.mul_sum _ _ _).symm
    _ <= (2 * C) * ((X : Real) * (y : Real) ^ (b - 1) / (1 - b)) :=
      _root_.mul_le_mul_of_nonneg_left
        (Real.sum_Icc_cofactor_rpow_le X y hX hy b hb0 hb1)
        (mul_nonneg (by norm_num) hC)
    _ = (2 * C / (1 - b)) * (X : Real) * (y : Real) ^ (b - 1) := by ring

/-- The quantitative smooth-number transfer, with the ordinary character sum retained. -/
theorem norm_sum_smoothNumbersUpTo_le_rpow (f : Nat -> Complex)
    (hmul : forall m p, f (m * p) = f m * f p)
    (X y : Nat) (hX : 0 < X) (hy : 0 < y)
    (b C : Real) (hb0 : 0 <= b) (hb1 : b < 1) (hC : 0 <= C)
    (hunit : forall m, Membership.mem (Finset.Icc 1 (X / y)) m -> norm (f m) <= 1)
    (hprefix : forall t, t <= X ->
      norm (Finset.sum (primesBelow (t + 1)) f) <= C * (t : Real) ^ b) :
    norm (Finset.sum (smoothNumbersUpTo X (y + 1)) f) <=
      norm (Finset.sum (Finset.Icc 1 X) f) +
        (2 * C / (1 - b)) * (X : Real) * (y : Real) ^ (b - 1) := by
  exact (norm_sum_smoothNumbersUpTo_le_prime_rows f hmul X y hy hunit).trans
    (_root_.add_le_add le_rfl
      (sum_norm_largestPrimeFactor_rows_le_rpow f X y hX hy b C hb0 hb1 hC hprefix))

/-- The same power bound transfers directly to the largest-prime-factor twist. -/
theorem norm_sum_largePrimeFactor_twist_le_rpow (f : Nat -> Complex)
    (X y : Nat) (hX : 0 < X) (hy : 0 < y)
    (b C : Real) (hb0 : 0 <= b) (hb1 : b < 1) (hC : 0 <= C)
    (hprefix : forall t, t <= X ->
      norm (Finset.sum (primesBelow (t + 1)) f) <= C * (t : Real) ^ b) :
    norm (Finset.sum ((Finset.Icc 1 X).filter (fun n => y < largestPrimeFactor n))
      (fun n => f (largestPrimeFactor n))) <=
      (2 * C / (1 - b)) * (X : Real) * (y : Real) ^ (b - 1) := by
  exact (norm_sum_largePrimeFactor_twist_le_prime_rows f X y hy).trans
    (sum_norm_largestPrimeFactor_rows_le_rpow f X y hX hy b C hb0 hb1 hC hprefix)

/-- Seven-eighths specialization of the complete row transfer; the prefix input stays explicit. -/
theorem sum_norm_largestPrimeFactor_rows_le_seven_eighths (f : Nat -> Complex)
    (X y : Nat) (hX : 0 < X) (hy : 0 < y) (C : Real) (hC : 0 <= C)
    (hprefix : forall t, t <= X ->
      norm (Finset.sum (primesBelow (t + 1)) f) <= C * (t : Real) ^ (7 / 8 : Real)) :
    Finset.sum (Finset.Icc 1 (X / y)) (fun m =>
      norm (Finset.sum (largestPrimeFactorRow X y m) f)) <=
      (16 * C) * (X : Real) * (y : Real) ^ (-(1 / 8 : Real)) := by
  have h := sum_norm_largestPrimeFactor_rows_le_rpow f X y hX hy
    (7 / 8) C (by norm_num) (by norm_num) hC hprefix
  have he : (7 / 8 : Real) - 1 = -(1 / 8 : Real) := by norm_num
  have hc : 2 * C / (1 - (7 / 8 : Real)) = 16 * C := by ring
  simpa only [he, hc] using h

end Nat
