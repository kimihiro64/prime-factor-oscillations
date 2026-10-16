/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# First-order Euler--Maclaurin summation

A Mathlib-only extraction of PrimeNumberTheoremAnd/EulerMaclaurin.lean at
commit 0f15a38c619298b5cd786d39a84dd4bb8997324c (Apache 2.0).
The original contributors' Abel-summation proof is adapted to ASCII syntax
and placed in the EulerMaclaurin namespace; the mathematical argument is unchanged.
Attribution: PrimeNumberTheoremAnd contributors and Prime Factor Oscillations contributors.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace EulerMaclaurin

variable {K : Type*} [RCLike K] {f : Real -> K} {a b : Real}

/-- The first periodic Bernoulli function on the nonnegative half-line. -/
def B1 (x : Real) : Real := x - Nat.floor x - 1 / 2

@[fun_prop]
theorem aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

theorem abs_B1_le_half {x : Real} (hx : 0 <= x) : abs (B1 x) <= 1 / 2 := by
  unfold B1
  refine abs_le.mpr (And.intro ?_ ?_)
  . have := Nat.floor_le hx
    linarith
  . have h := Nat.lt_succ_floor x
    simp only [Nat.cast_succ] at h
    linarith

theorem integral_deriv_mul_add_const (c : K) (hab : a <= b)
    (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : forall t : Real, Set.Icc a b t -> DifferentiableAt Real f t) :
    intervalIntegral (fun t : Real => ((t : K) + c) * deriv f t) a b volume =
      ((b : K) + c) * f b - ((a : K) + c) * f a -
        intervalIntegral f a b volume := by
  rw [<- Set.uIcc_of_le hab] at hf_diff
  have h : forall t : Real, Set.uIcc a b t ->
      HasDerivAt (fun t : Real => (t : K) + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := K)) using 1
    simp
  replace hf_diff := fun t ht => (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul h hf_diff (by simp) h_int]
  simp

theorem intervalIntegrable_deriv_mul_B1 (ha : 0 <= a) (hab : a <= b)
    (h_cont : ContinuousOn (deriv f) (Set.uIcc a b)) :
    IntervalIntegrable (fun t => deriv f t * (B1 t : K)) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

theorem integral_deriv_mul_floor_add_one (ha : 0 <= a) (hab : a <= b)
    (hf_diff : forall t : Real, Set.Icc a b t -> DifferentiableAt Real f t)
    (h_cont : ContinuousOn (deriv f) (Set.uIcc a b)) :
    intervalIntegral (fun t => deriv f t * ((Nat.floor t : K) + 1)) a b volume =
      ((b : K) + 1 / 2) * f b - ((a : K) + 1 / 2) * f a -
        intervalIntegral f a b volume -
        intervalIntegral (fun t => deriv f t * (B1 t : K)) a b volume := by
  calc
    _ = intervalIntegral (fun t => deriv f t * ((t : K) + 1 / 2) -
        deriv f t * (B1 t : K)) a b volume := by
      congr
      ext
      simp only [B1]
      push_cast
      ring
    _ = intervalIntegral (fun t => deriv f t * ((t : K) + 1 / 2)) a b volume -
        intervalIntegral (fun t => deriv f t * (B1 t : K)) a b volume := by
      exact intervalIntegral.integral_sub
        (ContinuousOn.intervalIntegrable (by fun_prop))
        (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
    _ = _ := by
      conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
      rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

/-- First-order Euler--Maclaurin, obtained from Abel summation. -/
theorem sum_eq_integral_add_integral_deriv (ha : 0 <= a) (hab : a <= b)
    (hf_diff : forall t : Real, Set.Icc a b t -> DifferentiableAt Real f t)
    (h_cont : ContinuousOn (deriv f) (Set.uIcc a b)) :
    Finset.sum (Finset.Ioc (Nat.floor a) (Nat.floor b)) (fun k => f (k : Real)) =
      f a * (B1 a : K) - f b * (B1 b : K) + intervalIntegral f a b volume +
        intervalIntegral (fun t => deriv f t * (B1 t : K)) a b volume := by
  have hC : ContinuousOn (deriv f) (Set.Icc a b) := by
    rw [<- Set.uIcc_of_le hab]
    exact h_cont
  have h := sum_mul_eq_sub_sub_integral_mul (fun _ => 1) ha hab hf_diff
    hC.integrableOn_Icc
  simp only [mul_one, Finset.sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at h
  rw [h, <- intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring

end EulerMaclaurin
