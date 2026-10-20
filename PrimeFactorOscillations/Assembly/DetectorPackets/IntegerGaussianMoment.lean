/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.SchwartzFrequencyTail

/-!
# IntegerGaussianMoment

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.IntegerGaussianMoment

open SchwartzFrequencyTail

theorem square_exp_bound (u : Real) (hu : 0 <= u) :
    u ^ 2 * Real.exp (-u) <= 2 := by
  have hSeries := Real.pow_div_factorial_le_exp u hu 2
  norm_num at hSeries
  have hs : u ^ 2 <= 2 * Real.exp u := by linarith
  calc
    _ <= (2 * Real.exp u) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _ = 2 := by rw [mul_assoc, <- Real.exp_add]; simp

theorem gaussian_second_term (a x : Real) (ha : 0 < a) (hx : 0 < x) :
    x ^ 2 * Real.exp (-a * x ^ 2) <= (2 / a ^ 2) * (1 / x ^ 2) := by
  have hb := square_exp_bound (a * x ^ 2) (mul_nonneg ha.le (sq_nonneg _))
  apply le_of_mul_le_mul_right _ (mul_pos (pow_pos ha 2) (pow_pos hx 2))
  calc
    _ = (a * x ^ 2) ^ 2 * Real.exp (-(a * x ^ 2)) := by ring
    _ <= 2 := hb
    _ = ((2 / a ^ 2) * (1 / x ^ 2)) * (a ^ 2 * x ^ 2) := by field_simp

theorem gaussian_int_second_term (a : Real) (ha : 0 < a) (n : Int) :
    (n : Real) ^ 2 * Real.exp (-a * (n : Real) ^ 2) <=
      (2 / a ^ 2) * (1 / (n.natAbs : Real) ^ 2) := by
  by_cases hn : n = 0
  . subst n
    simp
  . have hp : 0 < (n.natAbs : Real) := by
      exact_mod_cast (Int.natAbs_pos.mpr hn)
    have hs : (n.natAbs : Real) ^ 2 = (n : Real) ^ 2 := by
      rw [natAbs_real, sq_abs]
    rw [<- hs]
    exact gaussian_second_term a (n.natAbs : Real) ha hp

theorem finite_inverse_square_sum :
    exists B : Real, 0 < B /\ forall E : Finset Int,
      E.sum (fun n => 1 / (n.natAbs : Real) ^ 2) <= B := by
  choose A hA hTail using finite_int_power_tail 2 (by decide)
  refine Exists.intro (2 * A) (And.intro (by positivity) ?_)
  intro E
  let E0 := E.filter (fun n => Not (n = 0))
  have hSum : E.sum (fun n => 1 / (n.natAbs : Real) ^ 2) =
      E0.sum (fun n => 1 / (n.natAbs : Real) ^ 2) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hNot
    have hn0 : n = 0 := by
      by_contra h
      exact hNot (Finset.mem_filter.mpr (And.intro hn h))
    simp [hn0]
  have hSupport (n : Int) (hn : Membership.mem E0 n) :
      (1 / 2 : Real) < (n.natAbs : Real) := by
    have hNat : 0 < n.natAbs := Int.natAbs_pos.mpr (Finset.mem_filter.mp hn).2
    have hOne : (1 : Real) <= (n.natAbs : Real) := by exact_mod_cast hNat
    linarith
  rw [hSum]
  calc
    _ <= A / (1 / 2 : Real) ^ (2 - 1 : Nat) :=
      hTail (1 / 2) E0 (by norm_num) hSupport
    _ = 2 * A := by norm_num; ring

theorem finite_gaussian_second_moment :
    exists C : Real, 0 < C /\ forall (a : Real) (E : Finset Int), 0 < a ->
      E.sum (fun n => (n : Real) ^ 2 * Real.exp (-a * (n : Real) ^ 2)) <=
        C / a ^ 2 := by
  choose B hB hBound using finite_inverse_square_sum
  refine Exists.intro (2 * B) (And.intro (by positivity) ?_)
  intro a E ha
  calc
    _ <= E.sum (fun n => (2 / a ^ 2) * (1 / (n.natAbs : Real) ^ 2)) :=
      Finset.sum_le_sum (fun n hn => gaussian_int_second_term a ha n)
    _ = (2 / a ^ 2) * E.sum (fun n => 1 / (n.natAbs : Real) ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ <= (2 / a ^ 2) * B :=
      mul_le_mul_of_nonneg_left (hBound E) (by positivity)
    _ = (2 * B) / a ^ 2 := by ring

theorem gaussian_second_moment :
    exists C : Real, 0 < C /\ forall a : Real, 0 < a ->
      Summable (fun n : Int => (n : Real) ^ 2 * Real.exp (-a * (n : Real) ^ 2)) /\
      tsum (fun n : Int => (n : Real) ^ 2 * Real.exp (-a * (n : Real) ^ 2)) <=
        C / a ^ 2 := by
  choose C hC hFinite using finite_gaussian_second_moment
  refine Exists.intro C (And.intro hC ?_)
  intro a ha
  have hn : 0 <= (fun n : Int => (n : Real) ^ 2 * Real.exp (-a * (n : Real) ^ 2)) :=
    fun n => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hSum : Summable
      (fun n : Int => (n : Real) ^ 2 * Real.exp (-a * (n : Real) ^ 2)) :=
    summable_of_sum_le hn (fun E => hFinite a E ha)
  exact And.intro hSum (le_of_tendsto hSum.hasSum
    (Filter.Eventually.of_forall (fun E => hFinite a E ha)))

end PrimeFactorOscillations.IntegerGaussianMoment

