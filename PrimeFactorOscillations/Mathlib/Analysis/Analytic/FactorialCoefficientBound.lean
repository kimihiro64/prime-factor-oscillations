/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Geometric bounds for factorial-weighted coefficients

A geometric coefficient majorant controls the normalized finite polynomial
and its first derivative uniformly in the rank, including evaluation at zero.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem norm_descFactorial_div_pow_le_one (r j : Nat) (hr : 0 < r) :
    norm ((r.descFactorial j : Complex) / (r : Complex) ^ j) <= 1 := by
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  rw [norm_div, norm_pow]
  simp only [Complex.norm_natCast]
  apply (div_le_one (pow_pos hrR j)).mpr
  exact_mod_cast descFactorial_le_pow r j

theorem norm_descFactorial_coefficient_le_geometric
    (r : Nat) (hr : 0 < r) (c : Nat -> Complex)
    (A b R t : Real) (hA : 0 <= A) (ht : 0 <= t) (htb : t <= b)
    (hbR : b < R) (hc : forall j, norm (c j) <= A / R ^ j) :
    norm ((Finset.range (r + 1)).sum (fun j => c j * (t : Complex) ^ j *
      ((r.descFactorial j : Complex) / (r : Complex) ^ j))) <= A / (1 - b / R) := by
  have hb : 0 <= b := ht.trans htb
  have hR : 0 < R := hb.trans_lt hbR
  have hq : 0 <= b / R := div_nonneg hb hR.le
  have hq1 : b / R < 1 := (div_lt_one hR).mpr hbR
  have hqn : norm (b / R) < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq]
  have hs := (hasSum_geometric_of_norm_lt_one hqn).mul_left A
  have hmajor : forall j : Nat,
      norm (c j * (t : Complex) ^ j *
        ((r.descFactorial j : Complex) / (r : Complex) ^ j)) <= A * (b / R) ^ j := by
    intro j
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht]
    calc
      norm (c j) * t ^ j *
          norm ((r.descFactorial j : Complex) / (r : Complex) ^ j) <=
          (A / R ^ j) * b ^ j * 1 := by
        gcongr
        exact hc j
        exact norm_descFactorial_div_pow_le_one r j hr
      _ = A * (b / R) ^ j := by rw [div_pow]; ring
  calc
    norm ((Finset.range (r + 1)).sum (fun j => c j * (t : Complex) ^ j *
        ((r.descFactorial j : Complex) / (r : Complex) ^ j))) <=
        (Finset.range (r + 1)).sum (fun j => A * (b / R) ^ j) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hmajor j))
    _ <= A * (1 - b / R) ^ (-1 : Int) := by
      simpa using sum_le_hasSum (Finset.range (r + 1)) (fun j _ => by positivity) hs
    _ = A / (1 - b / R) := by simp [div_eq_mul_inv]

theorem norm_descFactorial_coefficient_deriv_le_geometric
    (r : Nat) (hr : 0 < r) (c : Nat -> Complex)
    (A b R t : Real) (hA : 0 <= A) (ht : 0 <= t) (htb : t <= b)
    (hbR : b < R) (hc : forall j, norm (c j) <= A / R ^ j) :
    norm ((Finset.range (r + 1)).sum (fun j => (j : Complex) * c j *
      (t : Complex) ^ (j - 1) *
      ((r.descFactorial j : Complex) / (r : Complex) ^ j))) <=
      A / (R * (1 - b / R) ^ 2) := by
  have hb : 0 <= b := ht.trans htb
  have hR : 0 < R := hb.trans_lt hbR
  have hq : 0 <= b / R := div_nonneg hb hR.le
  have hq1 : b / R < 1 := (div_lt_one hR).mpr hbR
  have hqn : norm (b / R) < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq]
  have hs : HasSum (fun j : Nat => (A / R) * ((j : Real) + 1) * (b / R) ^ j)
      ((A / R) * (1 / (1 - b / R) ^ 2)) := by
    simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, mul_assoc] using
      (hasSum_choose_mul_geometric_of_norm_lt_one 1 hqn).mul_left (A / R)
  have hmajor : forall j : Nat,
      norm (((j + 1 : Nat) : Complex) * c (j + 1) *
        (t : Complex) ^ j *
        ((r.descFactorial (j + 1) : Complex) / (r : Complex) ^ (j + 1))) <=
        (A / R) * ((j : Real) + 1) * (b / R) ^ j := by
    intro j
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht, Complex.norm_natCast]
    calc
      ((j + 1 : Nat) : Real) * norm (c (j + 1)) * t ^ j *
          norm ((r.descFactorial (j + 1) : Complex) / (r : Complex) ^ (j + 1)) <=
          ((j + 1 : Nat) : Real) * (A / R ^ (j + 1)) * b ^ j * 1 := by
        gcongr
        exact hc (j + 1)
        exact norm_descFactorial_div_pow_le_one r (j + 1) hr
      _ = (A / R) * ((j : Real) + 1) * (b / R) ^ j := by
        rw [div_pow, pow_succ, Nat.cast_add, Nat.cast_one]
        field_simp
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.add_sub_cancel]
  calc
    norm ((Finset.range r).sum (fun j => ((j + 1 : Nat) : Complex) * c (j + 1) *
        (t : Complex) ^ j *
        ((r.descFactorial (j + 1) : Complex) / (r : Complex) ^ (j + 1)))) <=
        (Finset.range r).sum
          (fun j => (A / R) * ((j : Real) + 1) * (b / R) ^ j) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hmajor j))
    _ <= (A / R) * (1 / (1 - b / R) ^ 2) :=
      sum_le_hasSum (Finset.range r) (fun j _ => by positivity) hs
    _ = A / (R * (1 - b / R) ^ 2) := by
      simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]

end Nat

