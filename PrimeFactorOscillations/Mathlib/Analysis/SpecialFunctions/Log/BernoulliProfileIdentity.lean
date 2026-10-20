/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.BernoulliProfileReconstruction

/-!
# Identity and common-tail cancellation for canonical Bernoulli profiles

Local equality or equality accumulating at a finite complex point determines
the whole profile. Splitting a common tail and cancelling it near one then
determines the remaining coordinates' profile. This is the input for the
finite exceptional-coordinate permutation in prime-profile rigidity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

/-- Every canonical profile is normalized to one at its centre. -/
theorem canonicalBernoulliProfile_one {I : Type*} (a : I -> Real) :
    canonicalBernoulliProfile a 1 = 1 := by
  simp [canonicalBernoulliProfile, canonicalBernoulliFactor]

/-- The canonical product splits over any subset and its complement. -/
theorem canonicalBernoulliProfile_split {I : Type*}
    (a : I -> Real) (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hs : Summable (fun i => (a i) ^ 2)) (S : Set I) (z : Complex) :
    canonicalBernoulliProfile a z =
      canonicalBernoulliProfile (fun i : S => a i.val) z *
        canonicalBernoulliProfile (fun i : S.compl => a i.val) z := by
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
  exact (Multipliable.tprod_mul_tprod_compl
    (f := fun i => canonicalBernoulliFactor (a i) z) (s := S) hS hSc).symm

/-- Equality near one point determines the complete entire profile. -/
theorem canonicalBernoulliProfile_eq_of_eventuallyEq {I J : Type*}
    (a : I -> Real) (b : J -> Real)
    (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hb : forall j, 0 <= b j) (hb1 : forall j, b j <= 1)
    (hsa : Summable (fun i => (a i) ^ 2)) (hsb : Summable (fun j => (b j) ^ 2))
    (z0 : Complex)
    (heq : Filter.EventuallyEq (nhds z0) (canonicalBernoulliProfile a)
      (canonicalBernoulliProfile b)) :
    canonicalBernoulliProfile a = canonicalBernoulliProfile b := by
  have hA : AnalyticOnNhd Complex (canonicalBernoulliProfile a) Set.univ :=
    fun z _ => (differentiable_canonicalBernoulliProfile a ha ha1 hsa).analyticAt z
  have hB : AnalyticOnNhd Complex (canonicalBernoulliProfile b) Set.univ :=
    fun z _ => (differentiable_canonicalBernoulliProfile b hb hb1 hsb).analyticAt z
  funext z
  exact (hA.eqOn_of_preconnected_of_eventuallyEq hB
    isPreconnected_univ (Set.mem_univ z0) heq) (Set.mem_univ z)

/-- A finite accumulation point of equality determines the entire profile. -/
theorem canonicalBernoulliProfile_eq_of_frequently_eq {I J : Type*}
    (a : I -> Real) (b : J -> Real)
    (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hb : forall j, 0 <= b j) (hb1 : forall j, b j <= 1)
    (hsa : Summable (fun i => (a i) ^ 2)) (hsb : Summable (fun j => (b j) ^ 2))
    (z0 : Complex)
    (heq : Filter.Frequently (fun z => canonicalBernoulliProfile a z =
      canonicalBernoulliProfile b z) (nhdsWithin z0 (Set.singleton z0).compl)) :
    canonicalBernoulliProfile a = canonicalBernoulliProfile b := by
  have hA : AnalyticOnNhd Complex (canonicalBernoulliProfile a) Set.univ :=
    fun z _ => (differentiable_canonicalBernoulliProfile a ha ha1 hsa).analyticAt z
  have hB : AnalyticOnNhd Complex (canonicalBernoulliProfile b) Set.univ :=
    fun z _ => (differentiable_canonicalBernoulliProfile b hb hb1 hsb).analyticAt z
  funext z
  exact (hA.eqOn_of_preconnected_of_frequently_eq hB
    isPreconnected_univ (Set.mem_univ z0) heq) (Set.mem_univ z)

/-- A common complementary tail can be cancelled from equal profiles. -/
theorem canonicalBernoulliProfile_restrict_eq_of_tail_eq {I : Type*}
    (a b : I -> Real) (S : Set I)
    (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hb : forall i, 0 <= b i) (hb1 : forall i, b i <= 1)
    (hsa : Summable (fun i => (a i) ^ 2)) (hsb : Summable (fun i => (b i) ^ 2))
    (hprofile : canonicalBernoulliProfile a = canonicalBernoulliProfile b)
    (htail : forall i : S.compl, a i.val = b i.val) :
    canonicalBernoulliProfile (fun i : S => a i.val) =
      canonicalBernoulliProfile (fun i : S => b i.val) := by
  let aS : S -> Real := fun i => a i.val
  let bS : S -> Real := fun i => b i.val
  let aT : S.compl -> Real := fun i => a i.val
  let bT : S.compl -> Real := fun i => b i.val
  have hsuba : Summable (fun i => (aS i) ^ 2) := hsa.comp_injective Subtype.val_injective
  have hsubb : Summable (fun i => (bS i) ^ 2) := hsb.comp_injective Subtype.val_injective
  have htaila : Summable (fun i => (aT i) ^ 2) := hsa.comp_injective Subtype.val_injective
  have htailProfile : canonicalBernoulliProfile aT = canonicalBernoulliProfile bT :=
    congrArg (fun f : S.compl -> Real => canonicalBernoulliProfile f) (funext htail)
  have hcont : ContinuousAt (canonicalBernoulliProfile aT) 1 :=
    (differentiable_canonicalBernoulliProfile aT (fun i => ha i.val)
      (fun i => ha1 i.val) htaila).continuous.continuousAt
  have hne : Filter.Eventually (fun z => Not (canonicalBernoulliProfile aT z = 0))
      (nhds 1) :=
    hcont.eventually_ne (by rw [canonicalBernoulliProfile_one]; exact one_ne_zero)
  apply canonicalBernoulliProfile_eq_of_eventuallyEq aS bS
    (fun i => ha i.val) (fun i => ha1 i.val)
    (fun i => hb i.val) (fun i => hb1 i.val) hsuba hsubb 1
  filter_upwards [hne] with z hz
  have heq := congrFun hprofile z
  rw [canonicalBernoulliProfile_split a ha ha1 hsa S z,
    canonicalBernoulliProfile_split b hb hb1 hsb S z] at heq
  change canonicalBernoulliProfile aS z * canonicalBernoulliProfile aT z =
    canonicalBernoulliProfile bS z * canonicalBernoulliProfile bT z at heq
  rw [<- htailProfile] at heq
  have hdiff : (canonicalBernoulliProfile aS z - canonicalBernoulliProfile bS z) *
      canonicalBernoulliProfile aT z = 0 := by
    linear_combination heq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hz)

end Complex
