/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

/-! # Exact integrals of the finite record jumps

A jump at p contributes its height times X-p to the integral. Reflection
transports the existing cutoff-indicator integral without deleting endpoint
values or introducing an unproved almost-everywhere identification.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def recordRightStep (p c x : Real) : Real := by
  classical
  exact if p <= x then c else 0

theorem recordRightStep_eq_indicator (p c : Real) :
    recordRightStep p c = (Set.Ici p).indicator (fun _ : Real => c) := by
  classical
  funext x
  simp only [recordRightStep, Set.indicator, Set.mem_Ici]

theorem recordRightStep_intervalIntegrable (p c a b : Real) :
    IntervalIntegrable (recordRightStep p c) MeasureTheory.volume a b := by
  rw [recordRightStep_eq_indicator]
  have h : IntervalIntegrable (fun _ : Real => c) MeasureTheory.volume a b :=
    intervalIntegrable_const
  exact And.intro (h.1.indicator measurableSet_Ici) (h.2.indicator measurableSet_Ici)

theorem recordRightStep_integral (p c a b : Real) (hap : a <= p) (hpb : p <= b) :
    intervalIntegral (recordRightStep p c) a b MeasureTheory.volume = c * (b - p) := by
  classical
  let f : Real -> Real := (Set.Iic (-p)).indicator (fun _ => c)
  have hreflect : (fun x : Real => f (-x)) = recordRightStep p c := by
    funext x
    simp only [f, Set.indicator, Set.mem_Iic, neg_le_neg_iff, recordRightStep]
  rw [<- hreflect, intervalIntegral.integral_comp_neg f]
  have hp : Membership.mem (Set.Icc (-b) (-a)) (-p) :=
    And.intro (neg_le_neg hpb) (neg_le_neg hap)
  change intervalIntegral ((Set.Iic (-p)).indicator (fun _ : Real => c))
    (-b) (-a) MeasureTheory.volume = _
  calc
    _ = intervalIntegral (fun _ : Real => c) (-b) (-p) MeasureTheory.volume :=
      @intervalIntegral.integral_indicator Real _ _ (fun _ : Real => c)
        MeasureTheory.volume (-b) (-p) (-a) hp
    _ = c * (b - p) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

theorem recordRightStep_sum_integral {I : Type*} (S : Finset I)
    (p c : I -> Real) (a b : Real)
    (hbound : forall i, Membership.mem S i -> And (a <= p i) (p i <= b)) :
    intervalIntegral (fun x => S.sum (fun i => recordRightStep (p i) (c i) x))
      a b MeasureTheory.volume = S.sum (fun i => c i * (b - p i)) := by
  rw [intervalIntegral.integral_finsetSum
    (fun i _ => recordRightStep_intervalIntegrable (p i) (c i) a b)]
  apply Finset.sum_congr rfl
  intro i hi
  exact recordRightStep_integral (p i) (c i) a b (hbound i hi).1 (hbound i hi).2

end PrimeFactorOscillations.PrimeClassDeletion
