/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Weighted variance with a positive baseline and the complete mean correction -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace Finset

def weightedVarianceNumerator {Iota : Type*} (S : Finset Iota) (w x : Iota -> Real) : Real :=
  Finset.sum S w * Finset.sum S (fun i => w i * (x i) ^ 2) -
    (Finset.sum S (fun i => w i * x i)) ^ 2

theorem weightedVarianceNumerator_pairwise {Iota : Type*} (S : Finset Iota)
    (w x : Iota -> Real) :
    2 * weightedVarianceNumerator S w x =
      Finset.sum S (fun i => Finset.sum S (fun j => w i * w j * (x i - x j) ^ 2)) := by
  let K := Finset.sum S w
  let R := Finset.sum S (fun i => w i * x i)
  let T := Finset.sum S (fun i => w i * (x i) ^ 2)
  have hInner : forall i, Finset.sum S (fun j => w i * w j * (x i - x j) ^ 2) =
      w i * (x i) ^ 2 * K - 2 * w i * x i * R + w i * T := by
    intro i
    calc
      _ = Finset.sum S (fun j => (w i * (x i) ^ 2) * w j -
          (2 * w i * x i) * (w j * x j) + w i * (w j * (x j) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          <- Finset.mul_sum, <- Finset.mul_sum, <- Finset.mul_sum]
  have hOuter : Finset.sum S (fun i => Finset.sum S
      (fun j => w i * w j * (x i - x j) ^ 2)) = 2 * weightedVarianceNumerator S w x := by
    calc
      _ = Finset.sum S (fun i =>
          K * (w i * (x i) ^ 2) - (2 * R) * (w i * x i) + T * w i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hInner]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          <- Finset.mul_sum, <- Finset.mul_sum, <- Finset.mul_sum]
        dsimp only [weightedVarianceNumerator, K, R, T]
        ring
  exact hOuter.symm

theorem weightedVarianceNumerator_nonneg {Iota : Type*} (S : Finset Iota)
    (w x : Iota -> Real) (hw : forall i, Membership.mem S i -> 0 <= w i) :
    0 <= weightedVarianceNumerator S w x := by
  have h := Finset.sum_nonneg (fun i hi => Finset.sum_nonneg
    (fun j hj => mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg (x i - x j))))
  rw [<- weightedVarianceNumerator_pairwise S w x] at h
  linarith only [h]

theorem weightedVarianceNumerator_le_of_pairwise {Iota : Type*} (S : Finset Iota)
    (w x z : Iota -> Real) (hw : forall i, Membership.mem S i -> 0 <= w i)
    (hGap : forall i j, Membership.mem S i -> Membership.mem S j ->
      (x i - x j) ^ 2 <= (z i - z j) ^ 2) :
    weightedVarianceNumerator S w x <= weightedVarianceNumerator S w z := by
  have h := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum
    (fun j hj => _root_.mul_le_mul_of_nonneg_left (hGap i j hi hj)
      (mul_nonneg (hw i hi) (hw j hj))))
  rw [<- weightedVarianceNumerator_pairwise S w x,
    <- weightedVarianceNumerator_pairwise S w z] at h
  linarith only [h]

theorem weighted_variance_baseline_lower {Iota : Type*} (S : Finset Iota)
    (w x : Iota -> Real) (q c : Real) (hq : 0 <= q)
    (hw : forall i, Membership.mem S i -> q <= w i)
    (hZero : Finset.sum S x = 0)
    (hSquare : forall i, Membership.mem S i -> c <= (x i) ^ 2) :
    let r := (S.card : Real)
    let K := Finset.sum S w
    q * K * Finset.sum S (fun i => (x i) ^ 2) + q * r * (K - q * r) * c <=
      weightedVarianceNumerator S w x := by
  dsimp only
  let r := (S.card : Real)
  let K := Finset.sum S w
  let b := fun i => w i - q
  let E := Finset.sum S b
  let R := Finset.sum S (fun i => b i * x i)
  let T := Finset.sum S (fun i => b i * (x i) ^ 2)
  let C := Finset.sum S (fun i => (x i) ^ 2)
  have hb : forall i, Membership.mem S i -> 0 <= b i :=
    fun i hi => sub_nonneg.mpr (hw i hi)
  have hE : E = K - q * r := by
    dsimp only [E, b, K, r]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hR : R = Finset.sum S (fun i => w i * x i) := by
    dsimp only [R, b]
    simp only [sub_mul, Finset.sum_sub_distrib, <- Finset.mul_sum, hZero,
      mul_zero, sub_zero]
  have hT : T = Finset.sum S (fun i => w i * (x i) ^ 2) - q * C := by
    dsimp only [T, b, C]
    simp only [sub_mul, Finset.sum_sub_distrib, <- Finset.mul_sum]
  have hCS := weightedVarianceNumerator_nonneg S b x hb
  change 0 <= E * T - R ^ 2 at hCS
  have hMin : E * c <= T := by
    calc
      _ = Finset.sum S (fun i => b i * c) := Finset.sum_mul S b c
      _ <= _ := Finset.sum_le_sum (fun i hi =>
        _root_.mul_le_mul_of_nonneg_left (hSquare i hi) (hb i hi))
  have hScale := _root_.mul_le_mul_of_nonneg_left hMin
    (mul_nonneg hq (Nat.cast_nonneg S.card))
  change q * K * C + q * r * (K - q * r) * c <= weightedVarianceNumerator S w x
  dsimp only [weightedVarianceNumerator]
  rw [<- hR]
  have hEnergy : K * Finset.sum S (fun i => w i * (x i) ^ 2) - R ^ 2 =
      q * K * C + q * r * T + (E * T - R ^ 2) := by
    rw [hE, hT]
    ring
  change q * K * C + q * r * (K - q * r) * c <=
    K * Finset.sum S (fun i => w i * (x i) ^ 2) - R ^ 2
  rw [hEnergy]
  rw [hE] at hScale
  nlinarith only [hScale, hCS]

end Finset
