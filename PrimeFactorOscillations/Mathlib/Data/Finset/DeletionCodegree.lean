/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Positivity
import PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Ring.FiberCovariance

/-!
# Joint deletion control through common-neighbor bounds

The same deleted input can affect many targets. Its entire degree is squared
before estimating, retaining the intersections between different targets.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

theorem sum_squared_degrees_le {I T : Type*} [DecidableEq T]
    (P : Finset I) (B : Finset T) (w : I -> T -> Real) (U K : Real)
    (hK : 0 <= K)
    (hDiag : forall t, Membership.mem B t -> Finset.sum P (fun p => (w p t) ^ 2) <= U)
    (hCross : forall t, Membership.mem B t -> forall s, Membership.mem B s ->
      Not (s = t) -> Finset.sum P (fun p => w p t * w p s) <= K) :
    Finset.sum P (fun p => (Finset.sum B (w p)) ^ 2) <=
      (B.card : Real) * U + (B.card : Real) ^ 2 * K := by
  have hExpand : Finset.sum P (fun p => (Finset.sum B (w p)) ^ 2) =
      Finset.sum B (fun t => Finset.sum B (fun s =>
        Finset.sum P (fun p => w p t * w p s))) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hExpand]
  calc
    _ <= Finset.sum B (fun t => U + (B.card : Real) * K) := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        _ <= Finset.sum B (fun s => (if s = t then U else 0) + K) := by
          apply Finset.sum_le_sum
          intro s hs
          by_cases he : s = t
          next =>
            subst s
            have hd := hDiag t ht
            simp only [ite_true, <- pow_two]
            linarith
          next =>
            simpa only [if_neg he, zero_add] using hCross t ht s hs he
        _ = _ := by simp [Finset.sum_add_distrib, ht]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem covered_target_card_le {I T : Type*} [DecidableEq I] [DecidableEq T]
    (P D : Finset I) (B : Finset T) (hDP : D <= P)
    (w : I -> T -> Real) (L U K : Real) (hL : 0 < L) (hU : 0 <= U) (hK : 0 <= K)
    (hCover : forall t, Membership.mem B t -> L <= 2 * Finset.sum D (fun p => w p t))
    (hDiag : forall t, Membership.mem B t -> Finset.sum P (fun p => (w p t) ^ 2) <= U)
    (hCross : forall t, Membership.mem B t -> forall s, Membership.mem B s ->
      Not (s = t) -> Finset.sum P (fun p => w p t * w p s) <= K)
    (hSmall : 8 * (D.card : Real) * K <= L ^ 2) :
    (B.card : Real) <= 8 * (D.card : Real) * U / L ^ 2 := by
  have hD : 0 <= (D.card : Real) := Nat.cast_nonneg _
  have hB : 0 <= (B.card : Real) := Nat.cast_nonneg _
  have hSum : (B.card : Real) * L <=
      2 * Finset.sum D (fun p => Finset.sum B (w p)) := by
    have h := Finset.sum_le_sum hCover
    simp only [Finset.sum_const, nsmul_eq_mul, <- Finset.mul_sum] at h
    rw [Finset.sum_comm] at h
    exact h
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq D (fun _ => (1 : Real))
    (fun p => Finset.sum B (w p))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  have hSubset : Finset.sum D (fun p => (Finset.sum B (w p)) ^ 2) <=
      Finset.sum P (fun p => (Finset.sum B (w p)) ^ 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hDP
    intro p hp hnot
    exact sq_nonneg _
  have hEnergy := sum_squared_degrees_le P B w U K hK hDiag hCross
  have hCombined := mul_le_mul_of_nonneg_left (hSubset.trans hEnergy) hD
  have hNonnegSum : 0 <= Finset.sum D (fun p => Finset.sum B (w p)) := by
    have := mul_nonneg hB hL.le
    linarith
  have hSquare : ((B.card : Real) * L) ^ 2 <=
      4 * (D.card : Real) * ((B.card : Real) * U + (B.card : Real) ^ 2 * K) := by
    have hSquared := mul_le_mul hSum hSum (mul_nonneg hB hL.le)
      (show 0 <= 2 * Finset.sum D (fun p => Finset.sum B (w p)) by positivity)
    nlinarith
  by_cases hb : (B.card : Real) = 0
  next =>
    rw [hb]
    exact div_nonneg (by positivity) (sq_nonneg L)
  next =>
    have hbPos : 0 < (B.card : Real) := lt_of_le_of_ne hB (Ne.symm hb)
    have hAbsorb := mul_le_mul_of_nonneg_right hSmall (sq_nonneg (B.card : Real))
    have hFinal : (B.card : Real) * ((B.card : Real) * L ^ 2) <=
        (B.card : Real) * (8 * (D.card : Real) * U) := by
      nlinarith only [hSquare, hAbsorb]
    have hScaled : (B.card : Real) * L ^ 2 <= 8 * (D.card : Real) * U := by
      by_contra hNo
      have hStrict := mul_lt_mul_of_pos_left (lt_of_not_ge hNo) hbPos
      exact (not_lt_of_ge hFinal) hStrict
    have hMul := mul_le_mul_of_nonneg_right hScaled (inv_nonneg.mpr (sq_nonneg L))
    have hCancel : ((B.card : Real) * L ^ 2) * Inv.inv (L ^ 2) = (B.card : Real) := by
      field_simp [ne_of_gt hL]
    rw [hCancel] at hMul
    simpa only [div_eq_mul_inv] using hMul

theorem covered_target_card_le_of_energy {I T : Type*} [DecidableEq I] [DecidableEq T]
    (P D : Finset I) (B : Finset T) (hDP : D <= P)
    (w : I -> T -> Real) (L U K : Real) (hL : 0 < L) (hU : 0 <= U)
    (hCover : forall t, Membership.mem B t -> L <= 2 * Finset.sum D (fun p => w p t))
    (hEnergy : Finset.sum P (fun p => (Finset.sum B (w p)) ^ 2) <=
      (B.card : Real) * U + (B.card : Real) ^ 2 * K)
    (hSmall : 8 * (D.card : Real) * K <= L ^ 2) :
    (B.card : Real) <= 8 * (D.card : Real) * U / L ^ 2 := by
  have hD : 0 <= (D.card : Real) := Nat.cast_nonneg _
  have hB : 0 <= (B.card : Real) := Nat.cast_nonneg _
  have hSum : (B.card : Real) * L <=
      2 * Finset.sum D (fun p => Finset.sum B (w p)) := by
    have h := Finset.sum_le_sum hCover
    simp only [Finset.sum_const, nsmul_eq_mul, <- Finset.mul_sum] at h
    rw [Finset.sum_comm] at h
    exact h
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq D (fun _ => (1 : Real))
    (fun p => Finset.sum B (w p))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  have hSubset : Finset.sum D (fun p => (Finset.sum B (w p)) ^ 2) <=
      Finset.sum P (fun p => (Finset.sum B (w p)) ^ 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hDP
    intro p hp hnot
    exact sq_nonneg _
  have hCombined := mul_le_mul_of_nonneg_left (hSubset.trans hEnergy) hD
  have hNonnegSum : 0 <= Finset.sum D (fun p => Finset.sum B (w p)) := by
    have := mul_nonneg hB hL.le
    linarith
  have hSquare : ((B.card : Real) * L) ^ 2 <=
      4 * (D.card : Real) * ((B.card : Real) * U + (B.card : Real) ^ 2 * K) := by
    have hSquared := mul_le_mul hSum hSum (mul_nonneg hB hL.le)
      (show 0 <= 2 * Finset.sum D (fun p => Finset.sum B (w p)) by positivity)
    nlinarith
  by_cases hb : (B.card : Real) = 0
  next =>
    rw [hb]
    exact div_nonneg (by positivity) (sq_nonneg L)
  next =>
    have hbPos : 0 < (B.card : Real) := lt_of_le_of_ne hB (Ne.symm hb)
    have hAbsorb := mul_le_mul_of_nonneg_right hSmall (sq_nonneg (B.card : Real))
    have hFinal : (B.card : Real) * ((B.card : Real) * L ^ 2) <=
        (B.card : Real) * (8 * (D.card : Real) * U) := by
      nlinarith only [hSquare, hAbsorb]
    have hScaled : (B.card : Real) * L ^ 2 <= 8 * (D.card : Real) * U := by
      by_contra hNo
      have hStrict := mul_lt_mul_of_pos_left (lt_of_not_ge hNo) hbPos
      exact (not_lt_of_ge hFinal) hStrict
    have hMul := mul_le_mul_of_nonneg_right hScaled (inv_nonneg.mpr (sq_nonneg L))
    have hCancel : ((B.card : Real) * L ^ 2) * Inv.inv (L ^ 2) = (B.card : Real) := by
      field_simp [ne_of_gt hL]
    rw [hCancel] at hMul
    simpa only [div_eq_mul_inv] using hMul

end Finset
