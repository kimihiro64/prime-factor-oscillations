/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliComparison

/-! # Uniform total change under a growing Bernoulli tilt

A reciprocal-square odds difference gives a summable tilted-coordinate kernel.
Its telescoping bound is uniform in both the cutoff and the tilt, supplying the
total-change input to finite Bernoulli coefficient replacement comparison.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

/-- An exact telescoping reciprocal-square majorant with its endpoint reserve. -/
theorem sum_shifted_reciprocal_sq_le (N : Nat) (u z : Real)
    (hu : 0 < u) (hz : 0 <= z) :
    (range N).sum (fun n => z / ((n : Real) + 1 + u) ^ 2) <=
      z / u - z / ((N : Real) + u) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hA : 0 < (N : Real) + u := add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) hu
    have hB : 0 < (N : Real) + 1 + u := by linarith only [hA]
    have hAB : (N : Real) + u <= (N : Real) + 1 + u := by linarith only
    have hh := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hA hAB)
      (div_nonneg hz hB.le)
    have hid : (1 / ((N : Real) + u)) * (z / ((N : Real) + 1 + u)) =
        z / ((N : Real) + u) - z / ((N : Real) + 1 + u) := by
      field_simp
      ring
    have hid' : (1 / ((N : Real) + 1 + u)) * (z / ((N : Real) + 1 + u)) =
        z / ((N : Real) + 1 + u) ^ 2 := by field_simp
    rw [hid, hid'] at hh
    rw [sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [ih, hh]

/-- The shifted tilt kernel has a cutoff- and tilt-independent bound. -/
theorem sum_tilt_kernel_le (N : Nat) (c z : Real)
    (hc : 0 < c) (hz : 0 < z) :
    (range N).sum (fun n => z / ((n : Real) + 1 + c * z) ^ 2) <=
      1 / c := by
  have hb := sum_shifted_reciprocal_sq_le N (c * z) z (mul_pos hc hz) hz.le
  have ht : 0 <= z / ((N : Real) + c * z) :=
    div_nonneg hz.le (add_nonneg (Nat.cast_nonneg N) (mul_pos hc hz).le)
  have hid : z / (c * z) = 1 / c := by field_simp
  rw [hid] at hb
  linarith only [hb, ht]

/-- Adding the zero index costs at most one further inverse-square constant. -/
theorem sum_tilt_kernel_unshifted_le (N : Nat) (c z : Real)
    (hc : 0 < c) (hz1 : 1 <= z) :
    (range N).sum (fun n => z / ((n : Real) + c * z) ^ 2) <=
      1 / c ^ 2 + 1 / c := by
  have hz : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have h0 : z / (c * z) ^ 2 <= 1 / c ^ 2 := by
    have hm : c ^ 2 <= c ^ 2 * z := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hz1 (sq_nonneg c)
    have hh := one_div_le_one_div_of_le (sq_pos_of_pos hc) hm
    have hid : z / (c * z) ^ 2 = 1 / (c ^ 2 * z) := by field_simp
    rwa [hid]
  cases N with
  | zero =>
    simp only [range_zero, sum_empty]
    exact add_nonneg (div_nonneg (by norm_num) (sq_nonneg c))
      (div_nonneg (by norm_num) hc.le)
  | succ N =>
    rw [sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add]
    have hb := sum_tilt_kernel_le N c z hc hz
    linarith only [hb, h0]

end Finset

namespace Real

/-- A second-order odds difference gives a decaying difference after tilting. -/
theorem abs_tiltOdds_sub_le_kernel (n : Nat) (hn : 1 <= n)
    (a b c K z : Real) (hc : 0 < c) (_hK : 0 <= K) (hz : 0 < z)
    (ha : c / (n : Real) <= a) (hb : c / (n : Real) <= b)
    (hd : abs (a - b) <= K / (n : Real) ^ 2) :
    abs (z * a / (1 + z * a) - z * b / (1 + z * b)) <=
      K * z / ((n : Real) + c * z) ^ 2 := by
  have hn0 : 0 < (n : Real) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have ha0 : 0 < a := (div_pos hc hn0).trans_le ha
  have hb0 : 0 < b := (div_pos hc hn0).trans_le hb
  have hda : 0 < 1 + z * a := by nlinarith only [mul_pos hz ha0]
  have hdb : 0 < 1 + z * b := by nlinarith only [mul_pos hz hb0]
  have hdz : 0 < (n : Real) + c * z := add_pos hn0 (mul_pos hc hz)
  have hpa := mul_le_mul_of_nonneg_right ha hn0.le
  have hpb := mul_le_mul_of_nonneg_right hb hn0.le
  have hca : c / (n : Real) * (n : Real) = c := by field_simp
  rw [hca] at hpa hpb
  have hla : (n : Real) + c * z <= (1 + z * a) * (n : Real) := by
    have hh := mul_le_mul_of_nonneg_left hpa hz.le
    nlinarith only [hh]
  have hlb : (n : Real) + c * z <= (1 + z * b) * (n : Real) := by
    have hh := mul_le_mul_of_nonneg_left hpb hz.le
    nlinarith only [hh]
  have hprod := mul_le_mul hla hlb hdz.le (mul_pos hda hn0).le
  have hden : ((n : Real) + c * z) ^ 2 <=
      ((1 + z * a) * (1 + z * b)) * (n : Real) ^ 2 := by
    nlinarith only [hprod]
  have hid : z * a / (1 + z * a) - z * b / (1 + z * b) =
      z * (a - b) / ((1 + z * a) * (1 + z * b)) := by
    field_simp
    ring
  have habs :
      abs (z * a / (1 + z * a) - z * b / (1 + z * b)) *
          ((1 + z * a) * (1 + z * b)) = z * abs (a - b) := by
    rw [hid, abs_div, abs_mul, abs_of_pos hz, abs_of_pos (mul_pos hda hdb)]
    field_simp
  have hbound := mul_le_mul_of_nonneg_right hd (sq_nonneg (n : Real))
  have hcancel : (K / (n : Real) ^ 2) * (n : Real) ^ 2 = K := by field_simp
  rw [hcancel] at hbound
  have hs := mul_le_mul_of_nonneg_left hbound hz.le
  have hx := mul_le_mul_of_nonneg_left hden
    (abs_nonneg (z * a / (1 + z * a) - z * b / (1 + z * b)))
  have hscaled :
      abs (z * a / (1 + z * a) - z * b / (1 + z * b)) *
        ((n : Real) + c * z) ^ 2 <= K * z := by
    calc
      _ <= abs (z * a / (1 + z * a) - z * b / (1 + z * b)) *
          (((1 + z * a) * (1 + z * b)) * (n : Real) ^ 2) := hx
      _ = (z * abs (a - b)) * (n : Real) ^ 2 := by rw [<- mul_assoc, habs]
      _ <= K * z := by nlinarith only [hs]
  have hh := mul_le_mul_of_nonneg_right hscaled
    (div_nonneg (show (0 : Real) <= 1 by norm_num) (sq_nonneg ((n : Real) + c * z)))
  have hid' : (abs (z * a / (1 + z * a) - z * b / (1 + z * b)) *
      ((n : Real) + c * z) ^ 2) * (1 / ((n : Real) + c * z) ^ 2) =
      abs (z * a / (1 + z * a) - z * b / (1 + z * b)) := by field_simp
  simpa only [hid', mul_one_div] using hh

end Real

namespace Finset

/-- Uniform total coordinate change, independent of cutoff and growing tilt.
The finite support may be any subset of the positive natural indices. -/
theorem sum_abs_tiltOdds_sub_le (S : Finset Nat) (N : Nat)
    (hSN : forall n, Membership.mem S n -> Membership.mem (range N) n)
    (a b : Nat -> Real)
    (c K z : Real) (hc : 0 < c) (hK : 0 <= K) (hz1 : 1 <= z)
    (hindex : forall n, Membership.mem S n -> 1 <= n)
    (ha : forall n, Membership.mem S n -> c / (n : Real) <= a n)
    (hb : forall n, Membership.mem S n -> c / (n : Real) <= b n)
    (hd : forall n, Membership.mem S n -> abs (a n - b n) <= K / (n : Real) ^ 2) :
    S.sum (fun n => abs (z * a n / (1 + z * a n) -
      z * b n / (1 + z * b n))) <= K * (1 / c ^ 2 + 1 / c) := by
  have hz : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  calc
    _ <= S.sum (fun n => K * (z / ((n : Real) + c * z) ^ 2)) := by
      apply sum_le_sum
      intro n hn
      have hh := Real.abs_tiltOdds_sub_le_kernel n (hindex n hn)
        (a n) (b n) c K z hc hK hz (ha n hn) (hb n hn) (hd n hn)
      simpa only [mul_div_assoc] using hh
    _ = K * S.sum (fun n => z / ((n : Real) + c * z) ^ 2) := by rw [mul_sum]
    _ <= K * (range N).sum (fun n => z / ((n : Real) + c * z) ^ 2) := by
      apply mul_le_mul_of_nonneg_left ?_ hK
      apply sum_le_sum_of_subset_of_nonneg hSN
      intro n hn hnot
      exact div_nonneg hz.le (sq_nonneg _)
    _ <= K * (1 / c ^ 2 + 1 / c) :=
      mul_le_mul_of_nonneg_left (sum_tilt_kernel_unshifted_le N c z hc hz1) hK

end Finset
