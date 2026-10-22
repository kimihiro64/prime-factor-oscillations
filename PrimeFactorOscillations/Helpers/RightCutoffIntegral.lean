/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Exact right-cutoff integrals with an arbitrary retained kernel -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem rightCutoff_integral (g : Real -> Real) (p a b : Real)
    (hap : a <= p) (hpb : p <= b) :
    intervalIntegral ((Set.Ici p).indicator g) a b MeasureTheory.volume =
      intervalIntegral g p b MeasureTheory.volume := by
  classical
  let f : Real -> Real := (Set.Iic (-p)).indicator (fun x => g (-x))
  have hreflect : (fun x : Real => f (-x)) = (Set.Ici p).indicator g := by
    funext x
    simp only [f, Set.indicator, Set.mem_Iic, Set.mem_Ici, neg_le_neg_iff, neg_neg]
  rw [<- hreflect, intervalIntegral.integral_comp_neg f]
  have hp : Membership.mem (Set.Icc (-b) (-a)) (-p) :=
    And.intro (neg_le_neg hpb) (neg_le_neg hap)
  calc
    _ = intervalIntegral (fun x : Real => g (-x)) (-b) (-p) MeasureTheory.volume :=
      @intervalIntegral.integral_indicator Real _ _ (fun x : Real => g (-x))
        MeasureTheory.volume (-b) (-p) (-a) hp
    _ = intervalIntegral g p b MeasureTheory.volume := by
      rw [intervalIntegral.integral_comp_neg]
      simp only [neg_neg]

end PrimeFactorOscillations.PrimeClassDeletion
