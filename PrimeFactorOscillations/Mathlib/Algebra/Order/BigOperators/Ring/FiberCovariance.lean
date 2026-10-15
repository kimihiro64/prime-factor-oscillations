/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Joint covariance after projection onto finite fibers

The positive projected mass and the complete centered remainder are retained
in one inequality. Empty fibers have mean zero; every consumer summation uses
only the finite image of the given index set.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

noncomputable def fiberMean {I J : Type*} [DecidableEq J]
    (s : Finset I) (g : I -> J) (f : I -> Real) (a : J) : Real :=
  Finset.sum (s.filter (fun i => g i = a)) f /
    (((s.filter (fun i => g i = a)).card : Nat) : Real)

theorem sum_sub_fiberMean_eq_zero {I J : Type*} [DecidableEq J]
    (s : Finset I) (g : I -> J) (f : I -> Real) (a : J) :
    Finset.sum (s.filter (fun i => g i = a)) (fun i => f i - fiberMean s g f a) = 0 := by
  let t := s.filter (fun i => g i = a)
  by_cases ht : t.card = 0
  next =>
    have he := Finset.card_eq_zero.mp ht
    change Finset.sum t (fun i => f i - fiberMean s g f a) = 0
    rw [he]
    simp
  next =>
    have hc : Not ((t.card : Real) = 0) := by exact_mod_cast ht
    change Finset.sum t (fun i => f i - Finset.sum t f / (t.card : Real)) = 0
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp [hc]
    ring

theorem sum_centered_mul_fiberConstant_eq_zero {I J : Type*} [DecidableEq J]
    (s : Finset I) (g : I -> J) (f : I -> Real) (h : J -> Real) :
    Finset.sum s (fun i => (f i - fiberMean s g f (g i)) * h (g i)) = 0 := by
  have hMap : forall i, Membership.mem s i -> Membership.mem (s.image g) (g i) :=
    fun i hi => Finset.mem_image_of_mem g hi
  have hFiber := Finset.sum_fiberwise_of_maps_to hMap
    (fun i => (f i - fiberMean s g f (g i)) * h (g i))
  rw [<- hFiber]
  apply Finset.sum_eq_zero
  intro a ha
  calc
    _ = Finset.sum (s.filter (fun i => g i = a))
        (fun i => (f i - fiberMean s g f a) * h a) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = Finset.sum (s.filter (fun i => g i = a))
        (fun i => f i - fiberMean s g f a) * h a := (Finset.sum_mul _ _ _).symm
    _ = 0 := by rw [sum_sub_fiberMean_eq_zero]; simp

theorem sum_fiberMean_mul_eq_projection {I J : Type*} [DecidableEq J]
    (s : Finset I) (g : I -> J) (f b : I -> Real) :
    Finset.sum s (fun i => fiberMean s g f (g i) * b i) =
      Finset.sum (s.image g) (fun a => fiberMean s g f a *
        Finset.sum (s.filter (fun i => g i = a)) b) := by
  have hMap : forall i, Membership.mem s i -> Membership.mem (s.image g) (g i) :=
    fun i hi => Finset.mem_image_of_mem g hi
  have hFiber := Finset.sum_fiberwise_of_maps_to hMap
    (fun i => fiberMean s g f (g i) * b i)
  rw [<- hFiber]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

theorem sum_mul_eq_fiber_projection_add_covariance {I J : Type*} [DecidableEq J]
    (s : Finset I) (g : I -> J) (f b : I -> Real) :
    Finset.sum s (fun i => f i * b i) =
      Finset.sum (s.image g) (fun a => fiberMean s g f a *
        Finset.sum (s.filter (fun i => g i = a)) b) +
      Finset.sum s (fun i => (f i - fiberMean s g f (g i)) *
        (b i - fiberMean s g b (g i))) := by
  rw [<- sum_fiberMean_mul_eq_projection]
  have hZero := sum_centered_mul_fiberConstant_eq_zero s g f (fiberMean s g b)
  calc
    _ = Finset.sum s (fun i => fiberMean s g f (g i) * b i +
        (f i - fiberMean s g f (g i)) * (b i - fiberMean s g b (g i)) +
        (f i - fiberMean s g f (g i)) * fiberMean s g b (g i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hZero, add_zero]

theorem fiber_projection_sub_covariance_le_sum_mul {I J : Type*} [DecidableEq J]
    (s : Finset I) (g : I -> J) (f b : I -> Real) :
    Finset.sum (s.image g) (fun a => fiberMean s g f a *
        Finset.sum (s.filter (fun i => g i = a)) b) -
      Real.sqrt (Finset.sum s (fun i => (f i - fiberMean s g f (g i)) ^ 2) *
        Finset.sum s (fun i => (b i - fiberMean s g b (g i)) ^ 2)) <=
      Finset.sum s (fun i => f i * b i) := by
  let F := fun i => f i - fiberMean s g f (g i)
  let B := fun i => b i - fiberMean s g b (g i)
  have hF : 0 <= Finset.sum s (fun i => (F i) ^ 2) :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hB : 0 <= Finset.sum s (fun i => (B i) ^ 2) :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hProduct := mul_nonneg hF hB
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s F B
  have hRoot := Real.sq_sqrt hProduct
  have hRootNonneg := Real.sqrt_nonneg
    (Finset.sum s (fun i => (F i) ^ 2) * Finset.sum s (fun i => (B i) ^ 2))
  have hLower : -Real.sqrt (Finset.sum s (fun i => (F i) ^ 2) *
      Finset.sum s (fun i => (B i) ^ 2)) <= Finset.sum s (fun i => F i * B i) := by
    nlinarith
  have hIdentity := sum_mul_eq_fiber_projection_add_covariance s g f b
  change _ - _ <= _
  dsimp [F, B] at hLower
  linarith

end Finset
