/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.BernoulliProfileMultiplicity

/-!
# Reconstruction of positive coordinates from a Bernoulli profile

Two admissible square-summable probability arrays have the same entire profile
exactly when their positive coordinates admit a value-preserving bijection.
Zero coordinates are invisible. Repeated values and values equal to one are
retained. This is the matching input for prime-labelled tail reconstruction.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

private def positiveParameterFibreEquiv {I : Type*} (a : I -> Real)
    (c : {r : Real // 0 < r}) :
    Equiv
      {i : {i : I // 0 < a i} //
        (Subtype.mk (a i.val) i.property : {r : Real // 0 < r}) = c}
      {i : I // a i = c.val} where
  toFun i := Subtype.mk i.val.val (congrArg Subtype.val i.property)
  invFun i := Subtype.mk
    (Subtype.mk i.val (by rw [i.property]; exact c.property))
    (Subtype.ext i.property)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equal profiles match every positive coordinate, including repetitions. -/
theorem exists_positive_equiv_of_canonicalBernoulliProfile_eq {I J : Type*}
    (a : I -> Real) (b : J -> Real)
    (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hb : forall j, 0 <= b j) (hb1 : forall j, b j <= 1)
    (hsa : Summable (fun i => (a i) ^ 2)) (hsb : Summable (fun j => (b j) ^ 2))
    (hprofile : canonicalBernoulliProfile a = canonicalBernoulliProfile b) :
    exists e : Equiv {i : I // 0 < a i} {j : J // 0 < b j},
      forall i, a i.val = b (e i).val := by
  classical
  let A := {i : I // 0 < a i}
  let B := {j : J // 0 < b j}
  let C := {r : Real // 0 < r}
  let fa : A -> C := fun i => Subtype.mk (a i.val) i.property
  let fb : B -> C := fun j => Subtype.mk (b j.val) j.property
  let values : forall c : C, Equiv {i : I // a i = c.val} {j : J // b j = c.val} := by
    intro c
    let : Fintype {i : I // a i = c.val} :=
      (finite_fibre_of_summable_sq a hsa c.val c.property).fintype
    let : Fintype {j : J // b j = c.val} :=
      (finite_fibre_of_summable_sq b hsb c.val c.property).fintype
    apply Fintype.equivOfCardEq
    simpa only [Nat.card_eq_fintype_card] using
      card_fibre_eq_of_canonicalBernoulliProfile_eq
        a b ha ha1 hb hb1 hsa hsb hprofile c.val c.property
  let fibres : forall c : C, Equiv {i : A // fa i = c} {j : B // fb j = c} :=
    fun c => (positiveParameterFibreEquiv a c).trans
      ((values c).trans (positiveParameterFibreEquiv b c).symm)
  let e : Equiv A B := (Equiv.sigmaFiberEquiv fa).symm.trans
    ((Equiv.sigmaCongrRight fibres).trans (Equiv.sigmaFiberEquiv fb))
  refine Exists.intro e ?_
  intro i
  exact (congrArg Subtype.val (fibres (fa i) (Subtype.mk i rfl)).property).symm

/-- Deleting all zero coordinates leaves the canonical product unchanged. -/
theorem canonicalBernoulliProfile_subtype_pos {I : Type*}
    (a : I -> Real) (ha : forall i, 0 <= a i) (z : Complex) :
    canonicalBernoulliProfile (fun i : {i : I // 0 < a i} => a i.val) z =
      canonicalBernoulliProfile a z := by
  unfold canonicalBernoulliProfile
  apply tprod_subtype_eq_of_mulSupport_subset
    (f := fun i => canonicalBernoulliFactor (a i) z) (s := {i | 0 < a i})
  intro i hi
  change 0 < a i
  by_contra hn
  have hz : a i = 0 := le_antisymm (le_of_not_gt hn) (ha i)
  exact hi (by simp [canonicalBernoulliFactor, hz])

/-- A value-preserving bijection of positive coordinates preserves the profile. -/
theorem canonicalBernoulliProfile_eq_of_positive_equiv {I J : Type*}
    (a : I -> Real) (b : J -> Real)
    (ha : forall i, 0 <= a i) (hb : forall j, 0 <= b j)
    (e : Equiv {i : I // 0 < a i} {j : J // 0 < b j})
    (he : forall i, a i.val = b (e i).val) :
    canonicalBernoulliProfile a = canonicalBernoulliProfile b := by
  funext z
  rw [<- canonicalBernoulliProfile_subtype_pos a ha z,
    <- canonicalBernoulliProfile_subtype_pos b hb z]
  calc
    canonicalBernoulliProfile (fun i : {i : I // 0 < a i} => a i.val) z =
        canonicalBernoulliProfile (fun i : {i : I // 0 < a i} => b (e i).val) z := by
      congr 1
      exact funext he
    _ = canonicalBernoulliProfile (fun j : {j : J // 0 < b j} => b j.val) z :=
      canonicalBernoulliProfile_comp_equiv (fun j => b j.val) e z

/-- The complete unlabelled inverse theorem, with zero coordinates omitted. -/
theorem canonicalBernoulliProfile_eq_iff_positive_equiv {I J : Type*}
    (a : I -> Real) (b : J -> Real)
    (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hb : forall j, 0 <= b j) (hb1 : forall j, b j <= 1)
    (hsa : Summable (fun i => (a i) ^ 2)) (hsb : Summable (fun j => (b j) ^ 2)) :
    canonicalBernoulliProfile a = canonicalBernoulliProfile b <->
      exists e : Equiv {i : I // 0 < a i} {j : J // 0 < b j},
        forall i, a i.val = b (e i).val := by
  constructor
  . exact exists_positive_equiv_of_canonicalBernoulliProfile_eq a b ha ha1 hb hb1 hsa hsb
  . intro h
    exact canonicalBernoulliProfile_eq_of_positive_equiv a b ha hb
      (Classical.choose h) (Classical.choose_spec h)

end Complex
