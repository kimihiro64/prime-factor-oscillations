/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Finite negative-power and cofactor sums

Integral comparison bounds every term in the cofactor range. For 0 <= b < 1,
the complete sum has the exact cost 1 / (1 - b). The floor-cutoff theorem
retains X * y^(b-1), rather than a weaker bound in an auxiliary variable.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Real

theorem sum_Icc_nat_rpow_neg_le (M : Nat) (b : Real) (hb0 : 0 <= b) (hb1 : b < 1) :
    Finset.sum (Finset.Icc 1 M) (fun m => (m : Real) ^ (-b)) <=
      (M : Real) ^ (1 - b) / (1 - b) := by
  let f : Real -> Real := fun t => t ^ (-b)
  have hanti : AntitoneOn f (Set.Ioc 0 (0 + (M : Real))) := by
    intro t ht u hu htu
    exact Real.rpow_le_rpow_of_nonpos ht.1 htu (neg_nonpos.mpr hb0)
  have hint : MeasureTheory.IntegrableOn f (Set.Icc 0 (0 + (M : Real))) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp
    exact intervalIntegral.intervalIntegrable_rpow' (neg_lt_neg hb1)
  have hbound := hanti.sum_le_integral_of_integrableOn hint
  have hset : Finset.Icc 1 M = Finset.Ico (0 + 1) (M + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.zero_add, Nat.lt_succ_iff]
  have hsum : Finset.sum (Finset.Icc 1 M) (fun m => (m : Real) ^ (-b)) =
      Finset.sum (Finset.range M) (fun i => f (0 + ((i + 1 : Nat) : Real))) := by
    rw [hset, <- Finset.sum_Ico_add (fun m : Nat => (m : Real) ^ (-b)) 0 M 1]
    simp only [Nat.Ico_zero_eq_range, Nat.add_comm 1, zero_add, f]
  rw [hsum]
  apply hbound.trans_eq
  dsimp only [f]
  rw [integral_rpow (Or.inl (neg_lt_neg hb1))]
  have he : -b + 1 = 1 - b := by ring
  rw [he, zero_add, Real.zero_rpow (ne_of_gt (sub_pos.mpr hb1)), sub_zero]


/-- Summing every cofactor retains the exponent, with its exact geometric cost. -/
theorem sum_Icc_div_nat_rpow_le (X : Real) (hX : 0 <= X)
    (M : Nat) (b : Real) (hb0 : 0 <= b) (hb1 : b < 1) :
    Finset.sum (Finset.Icc 1 M) (fun m => (X / (m : Real)) ^ b) <=
      X ^ b * (M : Real) ^ (1 - b) / (1 - b) := by
  have heq : Finset.sum (Finset.Icc 1 M) (fun m => (X / (m : Real)) ^ b) =
      X ^ b * Finset.sum (Finset.Icc 1 M) (fun m => (m : Real) ^ (-b)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Real.div_rpow hX (Nat.cast_nonneg m), Real.rpow_neg (Nat.cast_nonneg m),
      div_eq_mul_inv]
  rw [heq, div_eq_mul_inv, mul_assoc]
  exact mul_le_mul_of_nonneg_left (sum_Icc_nat_rpow_neg_le M b hb0 hb1)
    (Real.rpow_nonneg hX b)


/-- The actual floor cutoff gives the scale X * y^(b-1), with no lost power. -/
theorem sum_Icc_cofactor_rpow_le (X y : Nat) (hX : 0 < X) (hy : 0 < y)
    (b : Real) (hb0 : 0 <= b) (hb1 : b < 1) :
    Finset.sum (Finset.Icc 1 (X / y)) (fun m => ((X : Real) / (m : Real)) ^ b) <=
      (X : Real) * (y : Real) ^ (b - 1) / (1 - b) := by
  have hx : 0 < (X : Real) := Nat.cast_pos.mpr hX
  have hyR : 0 < (y : Real) := Nat.cast_pos.mpr hy
  have hraw : ((X / y : Nat) : Real) * (y : Real) <= (X : Real) := by
    exact_mod_cast Nat.div_mul_le_self X y
  have hfloor : ((X / y : Nat) : Real) <= (X : Real) / (y : Real) := by
    simpa [hyR.ne'] using div_le_div_of_nonneg_right hraw hyR.le
  calc
    _ <= (X : Real) ^ b * ((X / y : Nat) : Real) ^ (1 - b) / (1 - b) :=
      sum_Icc_div_nat_rpow_le (X : Real) hx.le (X / y) b hb0 hb1
    _ <= (X : Real) ^ b * ((X : Real) / (y : Real)) ^ (1 - b) / (1 - b) := by
      gcongr
    _ = (X : Real) * (y : Real) ^ (b - 1) / (1 - b) := by
      congr 1
      rw [Real.div_rpow hx.le hyR.le, div_eq_mul_inv, <- mul_assoc,
        <- Real.rpow_add hx]
      have he : b + (1 - b) = 1 := by ring
      have he' : -(1 - b) = b - 1 := by ring
      rw [he, Real.rpow_one, <- Real.rpow_neg hyR.le, he']

end Real
