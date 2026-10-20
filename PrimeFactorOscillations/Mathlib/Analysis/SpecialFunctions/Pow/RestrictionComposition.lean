/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite power-mean composition and scalar quadratic comparisons. -/

set_option maxRecDepth 100

namespace Real

/-- The coupled Holder step for the three-restriction argument.
This does not assert a restriction theorem for prime-supported weights. -/
theorem four_thirds_product_bound
    {I : Type*} (U : Finset I) (f g : I -> Real)
    (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i) :
    (Finset.sum U (fun i => (f i * g i) ^ (4 / 3 : Real))) ^ (3 / 2 : Real) <=
      (Finset.sum U (fun i => f i ^ (8 / 3 : Real))) ^ (3 / 4 : Real) *
      (Finset.sum U (fun i => g i ^ (8 / 3 : Real))) ^ (3 / 4 : Real) := by
  have hProduct :
      Finset.sum U (fun i => (f i * g i) ^ (4 / 3 : Real)) =
        Finset.sum U (fun i => f i ^ (4 / 3 : Real) * g i ^ (4 / 3 : Real)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.mul_rpow (hf i) (hg i)
  rw [hProduct]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq U
    (fun i => f i ^ (4 / 3 : Real)) (fun i => g i ^ (4 / 3 : Real))
  have hRoot := Real.rpow_le_rpow (sq_nonneg _) hCS
    (by norm_num : (0 : Real) <= 3 / 4)
  have hNonneg :
      0 <= Finset.sum U
        (fun i => f i ^ (4 / 3 : Real) * g i ^ (4 / 3 : Real)) := by
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (Real.rpow_nonneg (hf i) _) (Real.rpow_nonneg (hg i) _))
  have hLeft :
      ((Finset.sum U
        (fun i => f i ^ (4 / 3 : Real) * g i ^ (4 / 3 : Real))) ^ 2) ^
          (3 / 4 : Real) =
        (Finset.sum U
          (fun i => f i ^ (4 / 3 : Real) * g i ^ (4 / 3 : Real))) ^
            (3 / 2 : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hNonneg]
    norm_num
  have hPower (x : Real) (hx : 0 <= x) :
      (x ^ (4 / 3 : Real)) ^ 2 = x ^ (8 / 3 : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hx]
    norm_num
  have hFirst :
      Finset.sum U (fun i => (f i ^ (4 / 3 : Real)) ^ 2) =
        Finset.sum U (fun i => f i ^ (8 / 3 : Real)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hPower (f i) (hf i)
  have hSecond :
      Finset.sum U (fun i => (g i ^ (4 / 3 : Real)) ^ 2) =
        Finset.sum U (fun i => g i ^ (8 / 3 : Real)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hPower (g i) (hg i)
  rw [hLeft, Real.mul_rpow (by positivity) (by positivity), hFirst, hSecond] at hRoot
  exact hRoot

/-- The source constants still have to be proved for the arithmetic transforms.
This lemma composes their exact squared norm bounds, without a target axiom. -/
theorem three_restriction_energy_bound
    {I : Type*} (U : Finset I) (f g : I -> Real)
    (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i)
    (energy D Ef Eg : Real) (hD : 0 <= D)
    (hOutput : energy <= D *
      (Finset.sum U (fun i => (f i * g i) ^ (4 / 3 : Real))) ^ (3 / 2 : Real))
    (hFirst : (Finset.sum U (fun i => f i ^ (8 / 3 : Real))) ^
      (3 / 4 : Real) <= Ef)
    (hSecond : (Finset.sum U (fun i => g i ^ (8 / 3 : Real))) ^
      (3 / 4 : Real) <= Eg) :
    energy <= D * Ef * Eg := by
  have hFsum : 0 <= Finset.sum U (fun i => f i ^ (8 / 3 : Real)) :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hf i) _)
  have hGsum : 0 <= Finset.sum U (fun i => g i ^ (8 / 3 : Real)) :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hg i) _)
  have hEf : 0 <= Ef := le_trans (Real.rpow_nonneg hFsum _) hFirst
  have hEg : 0 <= Eg := le_trans (Real.rpow_nonneg hGsum _) hSecond
  have hHolder := four_thirds_product_bound U f g hf hg
  have hBounds :
      (Finset.sum U (fun i => f i ^ (8 / 3 : Real))) ^ (3 / 4 : Real) *
        (Finset.sum U (fun i => g i ^ (8 / 3 : Real))) ^ (3 / 4 : Real) <=
          Ef * Eg :=
    mul_le_mul hFirst hSecond (Real.rpow_nonneg hGsum _) hEf
  exact hOutput.trans ((mul_le_mul_of_nonneg_left
    (hHolder.trans hBounds) hD).trans_eq (mul_assoc D Ef Eg).symm)

theorem fresh_control_factor_square (a b beta : Real) :
    a ^ 2 * (1 - beta) ^ 2 + 2 * a * b * (1 + beta) + b ^ 2 =
      (a * beta - (a - b)) ^ 2 + 4 * a * b := by
  ring


/-- In the full-prefix benchmark, the positive first moment changes with beta.
The cross comparison holds even at degenerate endpoint parameters. -/
theorem prime_prefix_positive_control_no_gain
    (t beta : Real) (ht : 0 <= t) (htOne : t <= 1) (hb : 0 <= beta) :
    (1 - beta * t ^ 2) ^ 2 <= (1 + beta * t) ^ 2 - 4 * beta * t ^ 2 := by
  have htSq : t ^ 2 <= 1 := by nlinarith
  have hFirst : 0 <= 2 * beta * t * (1 - t) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr htOne)
  have hSecond : 0 <= (beta * t) ^ 2 * (1 - t ^ 2) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr htSq)
  apply sub_nonneg.mp
  have hIdentity :
      ((1 + beta * t) ^ 2 - 4 * beta * t ^ 2) -
        (1 - beta * t ^ 2) ^ 2 =
      2 * beta * t * (1 - t) + (beta * t) ^ 2 * (1 - t ^ 2) := by ring
  rw [hIdentity]
  exact add_nonneg hFirst hSecond

theorem prime_prefix_control_denominator_pos
    (t beta : Real) (ht : 0 <= t) (htOne : t < 1) (hb : 0 <= beta) :
    0 < (1 + beta * t) ^ 2 - 4 * beta * t ^ 2 := by
  have hFactor :
      (1 + beta * t) ^ 2 - 4 * beta * t ^ 2 =
        (1 - beta * t) ^ 2 + 4 * beta * t * (1 - t) := by ring
  rw [hFactor]
  by_cases hbt : beta * t = 0
  next =>
    rw [show 4 * beta * t * (1 - t) = 4 * (beta * t) * (1 - t) by ring,
      hbt]
    norm_num
  next =>
    have hbtPos : 0 < beta * t :=
      lt_of_le_of_ne (mul_nonneg hb ht) (Ne.symm hbt)
    have hPos := mul_pos (by norm_num : (0 : Real) < 4)
      (mul_pos hbtPos (sub_pos.mpr htOne))
    have hTerm : 0 < 4 * beta * t * (1 - t) := by nlinarith only [hPos]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hTerm

theorem prime_prefix_negative_control_no_gain
    (t gamma : Real) (ht : 0 <= t) (htOne : t <= 1) (hg : 0 <= gamma) :
    (1 + gamma * t ^ 2) ^ 2 <= (1 + gamma * t) ^ 2 := by
  have htSq : t ^ 2 <= t := by nlinarith
  have hLeft : 0 <= gamma * (t - t ^ 2) :=
    mul_nonneg hg (sub_nonneg.mpr htSq)
  have hRight : 0 <= 2 + gamma * t + gamma * t ^ 2 := by positivity
  have h := mul_nonneg hLeft hRight
  nlinarith only [h]

/-- The lower constant floor from the selected major arcs already exceeds 9.
The analytic hypotheses that produce this floor are not formalized here. -/
theorem separate_restriction_constant_square_gap :
    (81 : Real) < (25 / 8 : Real) ^ 2 * (195 / 128 : Real) *
      (85 / 48 : Real) ^ 3 := by
  norm_num

theorem full_prefix_restriction_score_ceiling
    (A C : Real) (hA : A ^ 2 <= 242 / 29) (hC : 9 < C) :
    A ^ 2 / C - 1 < -(19 / 261 : Real) := by
  have hCPos : 0 < C := by linarith
  have hCore : A ^ 2 < (242 / 261 : Real) * C := by linarith
  have hCancel : (A ^ 2 / C) * C = A ^ 2 := by
    field_simp [ne_of_gt hCPos]
  have hMult : (A ^ 2 / C) * C < (242 / 261 : Real) * C := by
    rw [hCancel]
    exact hCore
  have hRatio := (mul_lt_mul_iff_of_pos_right hCPos).mp hMult
  linarith

end Real
