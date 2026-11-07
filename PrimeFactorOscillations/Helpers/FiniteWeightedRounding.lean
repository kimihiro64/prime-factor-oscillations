/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Weighted threshold rounding with every variance cross term retained -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

def halfRoundIndicator (y : Real) : Real := by
  classical
  exact if 1 / 2 <= y then 1 else 0

theorem finiteWeightedVariance_expansion {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (z : Real) :
    Finset.sum S (fun i => a i * (y i - z) ^ 2) =
      Finset.sum S (fun i => a i * (y i) ^ 2) -
        2 * z * Finset.sum S (fun i => a i * y i) + z ^ 2 * Finset.sum S a := by
  calc
    _ = Finset.sum S (fun i => a i * (y i) ^ 2 - 2 * z * (a i * y i) + z ^ 2 * a i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum, <- Finset.mul_sum]

theorem finiteWeightedVariance_nonneg {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (z : Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i) :
    0 <= Finset.sum S (fun i => a i * (y i - z) ^ 2) :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))

theorem finiteWeightedSquareSum_le {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hN : 0 < Finset.sum S a) :
    (Finset.sum S (fun i => a i * y i)) ^ 2 <=
      Finset.sum S a * Finset.sum S (fun i => a i * (y i) ^ 2) := by
  let N := Finset.sum S a
  let M := Finset.sum S (fun i => a i * y i)
  let z := M / N
  have hNp : 0 < N := hN
  have hExpansion := finiteWeightedVariance_expansion S a y z
  have hScaled : N * Finset.sum S (fun i => a i * (y i - z) ^ 2) =
      N * Finset.sum S (fun i => a i * (y i) ^ 2) - M ^ 2 := by
    rw [hExpansion]
    change N * (Finset.sum S (fun i => a i * (y i) ^ 2) - 2 * z * M + z ^ 2 * N) = _
    dsimp only [z]
    field_simp [hNp.ne']
    ring
  have hNonneg := mul_nonneg (le_of_lt hNp) (finiteWeightedVariance_nonneg S a y z ha)
  rw [hScaled] at hNonneg
  change M ^ 2 <= N * Finset.sum S (fun i => a i * (y i) ^ 2)
  linarith

theorem halfRoundIndicator_square_error (y : Real) (hy : 0 <= y) :
    (y - halfRoundIndicator y) ^ 2 <= 2 * y * (y - 1) ^ 2 := by
  classical
  unfold halfRoundIndicator
  by_cases hHalf : 1 / 2 <= y
  case pos =>
    rw [ite_eq_left hHalf]
    have hProduct := mul_nonneg (show 0 <= 2 * y - 1 by linarith) (sq_nonneg (y - 1))
    nlinarith
  case neg =>
    rw [ite_eq_right hHalf]
    have hyHalf : y < 1 / 2 := lt_of_not_ge hHalf
    have hProduct := mul_nonneg hy
      (mul_nonneg (show 0 <= 1 - 2 * y by linarith) (show 0 <= 2 - y by linarith))
    nlinarith

theorem finiteWeightedRound_deviation {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i) (hN : 0 < Finset.sum S a) :
    (Finset.sum S (fun i => a i * y i) -
      Finset.sum S (fun i => a i * halfRoundIndicator (y i))) ^ 2 <=
        2 * Finset.sum S a * Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  have hVariance := finiteWeightedSquareSum_le S a (fun i => y i - halfRoundIndicator (y i)) ha hN
  have hDiff : Finset.sum S (fun i => a i * (y i - halfRoundIndicator (y i))) =
      Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * halfRoundIndicator (y i)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hDiff] at hVariance
  have hPoint : Finset.sum S (fun i => a i * (y i - halfRoundIndicator (y i)) ^ 2) <=
      2 * Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
    calc
      _ <= Finset.sum S (fun i => a i * (2 * y i * (y i - 1) ^ 2)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact _root_.mul_le_mul_of_nonneg_left (halfRoundIndicator_square_error (y i) (hy i hi)) (ha i hi)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hTotal := _root_.mul_le_mul_of_nonneg_left hPoint (le_of_lt hN)
  nlinarith only [hVariance, hTotal]

theorem finiteWeighted_div_sum {Iota : Type*} (S : Finset Iota) (a x : Iota -> Real) (t : Real) :
    Finset.sum S (fun i => a i * (x i / t)) =
      Finset.sum S (fun i => a i * x i) / t := by
  have h := (Finset.sum_mul S (fun i => a i * x i) (1 / t)).symm
  simpa only [div_eq_mul_inv, one_mul, mul_assoc] using h

theorem finiteWeighted_rescale_energy (x t : Real) (ht : 0 < t) :
    t ^ 3 * ((x / t) * (x / t - 1) ^ 2) = x * (x - t) ^ 2 := by
  field_simp [ht.ne']

theorem finiteWeightedRound_scaled {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> 0 <= x i) (hN : 0 < Finset.sum S a) :
    t ^ 3 * (Finset.sum S (fun i => a i * x i) / t -
      Finset.sum S (fun i => a i * halfRoundIndicator (x i / t))) ^ 2 <=
        2 * Finset.sum S a * Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
  have hRound := finiteWeightedRound_deviation S a (fun i => x i / t) ha
    (fun i hi => div_nonneg (hx i hi) (le_of_lt ht)) hN
  rw [finiteWeighted_div_sum] at hRound
  have hScaled := _root_.mul_le_mul_of_nonneg_left hRound (pow_nonneg (le_of_lt ht) 3)
  have hEnergy : t ^ 3 * Finset.sum S (fun i => a i * (x i / t) * (x i / t - 1) ^ 2) =
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := congrArg (fun q : Real => a i * q) (finiteWeighted_rescale_energy (x i) t ht)
    nlinarith only [h]
  have hRight : t ^ 3 * (2 * Finset.sum S a *
      Finset.sum S (fun i => a i * (x i / t) * (x i / t - 1) ^ 2)) =
        2 * Finset.sum S a * Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
    calc
      _ = 2 * Finset.sum S a * (t ^ 3 *
          Finset.sum S (fun i => a i * (x i / t) * (x i / t - 1) ^ 2)) := by ring
      _ = _ := by rw [hEnergy]
  rw [hRight] at hScaled
  exact hScaled

end PrimeFactorOscillations
