/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.BernoulliProfileZeros

/-!
# Partition and rescaling of canonical Bernoulli profiles

An arbitrary support partition splits the entire compensated product exactly.
Zero extension agrees with restriction to a subtype. Scaling probabilities
corresponds to an affine change of the profile variable centred at one.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

/-- Zero extension has exactly the profile of the restricted parameter array. -/
theorem canonicalBernoulliProfile_subtype_eq_indicator {I : Type*}
    (a : I -> Real) (S : Set I) (z : Complex) :
    canonicalBernoulliProfile (fun i : S => a i.val) z =
      canonicalBernoulliProfile (S.indicator a) z := by
  classical
  unfold canonicalBernoulliProfile
  rw [tprod_subtype S (fun i => canonicalBernoulliFactor (a i) z)]
  apply tprod_congr
  intro i
  by_cases hi : Membership.mem S i
  { simp [Set.mulIndicator, Set.indicator, hi] }
  { simp [Set.mulIndicator, Set.indicator, hi, canonicalBernoulliFactor] }

/-- Exact splitting on any support, including infinite supports and factor zeros. -/
theorem canonicalBernoulliProfile_partition {I : Type*}
    (a : I -> Real) (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hs : Summable (fun i => (a i) ^ 2)) (S : Set I) (z : Complex) :
    canonicalBernoulliProfile a z =
      canonicalBernoulliProfile (S.indicator a) z *
        canonicalBernoulliProfile (S.compl.indicator a) z := by
  classical
  have hnorm := summable_norm_canonicalBernoulliFactor_sub_one a ha ha1 hs z
  have hS : Multipliable (fun i : S => canonicalBernoulliFactor (a i.val) z) := by
    have h := multipliable_one_add_of_summable
      (hnorm.comp_injective (Subtype.val_injective : Function.Injective (fun i : S => i.val)))
    simpa only [Function.comp_def, add_sub_cancel] using h
  have hSc : Multipliable (fun i : S.compl => canonicalBernoulliFactor (a i.val) z) := by
    have h := multipliable_one_add_of_summable
      (hnorm.comp_injective
        (Subtype.val_injective : Function.Injective (fun i : S.compl => i.val)))
    simpa only [Function.comp_def, add_sub_cancel] using h
  have hsplit := (Multipliable.tprod_mul_tprod_compl
    (f := fun i => canonicalBernoulliFactor (a i) z) (s := S) hS hSc).symm
  change canonicalBernoulliProfile a z =
    canonicalBernoulliProfile (fun i : S => a i.val) z *
      canonicalBernoulliProfile (fun i : S.compl => a i.val) z at hsplit
  rw [canonicalBernoulliProfile_subtype_eq_indicator a S z,
    canonicalBernoulliProfile_subtype_eq_indicator a S.compl z] at hsplit
  exact hsplit

/-- Probability scaling is an affine profile change centred at one. -/
theorem canonicalBernoulliProfile_scale {I : Type*}
    (a : I -> Real) (c : Real) (z : Complex) :
    canonicalBernoulliProfile (fun i => c * a i) z =
      canonicalBernoulliProfile a (1 + (c : Complex) * (z - 1)) := by
  unfold canonicalBernoulliProfile
  apply tprod_congr
  intro i
  unfold canonicalBernoulliFactor
  congr 1 <;> congr 1 <;> push_cast <;> ring

end Complex
