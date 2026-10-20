/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.BernoulliProfileIdentity

/-!
# Finite exceptional permutations of Bernoulli coordinates

For arrays on the same finite index type, the profile determines all
coordinates up to a permutation, including zeros. If two infinite arrays
already agree outside a fixed prefix, equal profiles therefore give a
value-preserving permutation fixing that entire complementary tail.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

/-- On a fixed finite index set, the profile recovers zeros as well as positives. -/
theorem exists_perm_of_canonicalBernoulliProfile_eq {I : Type*} [Fintype I]
    (a b : I -> Real)
    (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hb : forall i, 0 <= b i) (hb1 : forall i, b i <= 1)
    (hprofile : canonicalBernoulliProfile a = canonicalBernoulliProfile b) :
    exists e : Equiv.Perm I, forall i, a i = b (e i) := by
  classical
  have hsa : Summable (fun i => (a i) ^ 2) := (hasSum_fintype _).summable
  have hsb : Summable (fun i => (b i) ^ 2) := (hasSum_fintype _).summable
  have hpos := exists_positive_equiv_of_canonicalBernoulliProfile_eq
    a b ha ha1 hb hb1 hsa hsb hprofile
  let ep := Classical.choose hpos
  have hep : forall i : {i : I // 0 < a i}, a i.val = b (ep i).val :=
    Classical.choose_spec hpos
  let : Fintype {i : I // 0 < a i} := Fintype.ofFinite _
  let : Fintype {i : I // 0 < b i} := Fintype.ofFinite _
  let : Fintype {i : I // Not (0 < a i)} := Fintype.ofFinite _
  let : Fintype {i : I // Not (0 < b i)} := Fintype.ofFinite _
  have hpCard : Fintype.card {i : I // 0 < a i} = Fintype.card {i : I // 0 < b i} :=
    Fintype.card_congr ep
  have hcCard : Fintype.card {i : I // Not (0 < a i)} =
      Fintype.card {i : I // Not (0 < b i)} := by
    rw [Fintype.card_subtype_compl (fun i => 0 < a i),
      Fintype.card_subtype_compl (fun i => 0 < b i), hpCard]
  let ec : Equiv {i : I // Not (0 < a i)} {i : I // Not (0 < b i)} :=
    Fintype.equivOfCardEq hcCard
  let e : Equiv.Perm I := Equiv.subtypeCongr ep ec
  refine Exists.intro e ?_
  intro i
  by_cases hi : 0 < a i
  . simpa [e, Equiv.subtypeCongr, Equiv.sumCompl, hi] using hep (Subtype.mk i hi)
  . have ha0 : a i = 0 := le_antisymm (le_of_not_gt hi) (ha i)
    have hb0 : b (ec (Subtype.mk i hi)).val = 0 :=
      le_antisymm (le_of_not_gt (ec (Subtype.mk i hi)).property)
        (hb (ec (Subtype.mk i hi)).val)
    have heval : e i = (ec (Subtype.mk i hi)).val := by
      simp [e, Equiv.subtypeCongr, Equiv.sumCompl, hi]
    rw [heval, ha0, hb0]

/-- A finite profile class is exactly a permutation class of the full arrays. -/
theorem canonicalBernoulliProfile_eq_iff_perm {I : Type*} [Fintype I]
    (a b : I -> Real)
    (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hb : forall i, 0 <= b i) (hb1 : forall i, b i <= 1) :
    canonicalBernoulliProfile a = canonicalBernoulliProfile b <->
      exists e : Equiv.Perm I, forall i, a i = b (e i) := by
  constructor
  . exact exists_perm_of_canonicalBernoulliProfile_eq a b ha ha1 hb hb1
  . intro h
    let e := Classical.choose h
    have he : a = fun i => b (e i) := funext (Classical.choose_spec h)
    rw [he]
    funext z
    exact canonicalBernoulliProfile_comp_equiv b e z

/-- Equal profiles and a common tail give a permutation fixing that entire tail. -/
theorem exists_bounded_perm_of_canonicalBernoulliProfile_eq
    (a b : Nat -> Real) (N : Nat)
    (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hb : forall i, 0 <= b i) (hb1 : forall i, b i <= 1)
    (hsa : Summable (fun i => (a i) ^ 2)) (hsb : Summable (fun i => (b i) ^ 2))
    (hprofile : canonicalBernoulliProfile a = canonicalBernoulliProfile b)
    (htail : forall n, N <= n -> a n = b n) :
    exists e : Equiv.Perm Nat,
      (forall n, N <= n -> e n = n) /\ forall n, a n = b (e n) := by
  classical
  let S : Set Nat := Set.Iio N
  let : Fintype S := (Set.finite_Iio N).fintype
  have hhead : canonicalBernoulliProfile (fun i : S => a i.val) =
      canonicalBernoulliProfile (fun i : S => b i.val) :=
    canonicalBernoulliProfile_restrict_eq_of_tail_eq a b S ha ha1 hb hb1 hsa hsb hprofile
      (fun i => htail i.val (le_of_not_gt i.property))
  have hperm := exists_perm_of_canonicalBernoulliProfile_eq
    (fun i : S => a i.val) (fun i : S => b i.val)
    (fun i => ha i.val) (fun i => ha1 i.val)
    (fun i => hb i.val) (fun i => hb1 i.val) hhead
  let es := Classical.choose hperm
  have hes := Classical.choose_spec hperm
  let e : Equiv.Perm Nat := Equiv.Perm.ofSubtype es
  have hfix : forall n, N <= n -> e n = n := by
    intro n hn
    exact Equiv.Perm.ofSubtype_apply_of_not_mem es (not_lt_of_ge hn)
  refine Exists.intro e (And.intro hfix ?_)
  intro n
  by_cases hn : n < N
  . have heval : e n = (es (Subtype.mk n hn)).val :=
      Equiv.Perm.ofSubtype_apply_of_mem es hn
    rw [heval]
    exact hes (Subtype.mk n hn)
  . rw [hfix n (le_of_not_gt hn)]
    exact htail n (le_of_not_gt hn)

end Complex
