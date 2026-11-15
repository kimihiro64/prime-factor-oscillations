/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianWickProfileOwnership

/-! # Complete Wick degree-assignment/profile bijection

The inverse retains the exact support and every block multiplicity.
No order on the vertex type and no independent-support relaxation is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {J : Type*} [Fintype J] [DecidableEq J]

def wickDegreesOfComposition {m : Nat} (S : Finset J) (d : Composition m)
    (hLen : d.length = S.card) : Finsupp J Nat :=
  Finsupp.equivFunOnFinite.symm (fun j =>
    if hj : Membership.mem S j then
      d.blocksFun (Fin.cast hLen.symm
        ((wickSupportIndexEquiv S).symm (Subtype.mk j hj)))
    else 0)

theorem wickDegreesOfComposition_apply {m : Nat} (S : Finset J) (d : Composition m)
    (hLen : d.length = S.card) (j : J) :
    wickDegreesOfComposition S d hLen j =
      if hj : Membership.mem S j then
        d.blocksFun (Fin.cast hLen.symm
          ((wickSupportIndexEquiv S).symm (Subtype.mk j hj)))
      else 0 := by
  rfl

theorem wickDegreesOfComposition_label {m : Nat} (S : Finset J) (d : Composition m)
    (hLen : d.length = S.card) (i : Fin S.card) :
    wickDegreesOfComposition S d hLen (wickSupportLabel S i) =
      d.blocksFun (Fin.cast hLen.symm i) := by
  rw [wickDegreesOfComposition_apply, dite_eq_left (wickSupportLabel_mem S i)]
  have hSub : Subtype.mk (wickSupportLabel S i) (wickSupportLabel_mem S i) =
      wickSupportIndexEquiv S i := by
    apply Subtype.ext
    exact (wickSupportIndexEquiv_val S i).symm
  rw [hSub, Equiv.symm_apply_apply]

theorem wickDegreesOfComposition_support {m : Nat} (S : Finset J) (d : Composition m)
    (hLen : d.length = S.card) :
    (wickDegreesOfComposition S d hLen).support = S := by
  ext j
  rw [Finsupp.mem_support_iff, wickDegreesOfComposition_apply]
  by_cases hj : Membership.mem S j
  case pos =>
    rw [dite_eq_left hj]
    have hPos := d.one_le_blocksFun
      (Fin.cast hLen.symm ((wickSupportIndexEquiv S).symm (Subtype.mk j hj)))
    exact Iff.intro (fun _ => hj) (fun _ => by omega)
  case neg =>
    rw [dite_eq_right hj]
    simp [hj]

theorem wickDegreesOfComposition_sum {m : Nat} (S : Finset J) (d : Composition m)
    (hLen : d.length = S.card) :
    Finset.sum Finset.univ (fun j => wickDegreesOfComposition S d hLen j) = m := by
  let l := wickDegreesOfComposition S d hLen
  let E : Equiv (Fin S.card) (Fin d.length) :=
    { toFun := Fin.cast hLen.symm
      invFun := Fin.cast hLen
      left_inv := by intro i; apply Fin.ext; rfl
      right_inv := by intro i; apply Fin.ext; rfl }
  have hSubset : Finset.sum S (fun j => l j) = Finset.sum Finset.univ (fun j => l j) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j hj hNot
    exact Finsupp.notMem_support_iff.mp (by
      rw [wickDegreesOfComposition_support]
      exact hNot)
  calc
    _ = Finset.sum S (fun j => l j) := hSubset.symm
    _ = Finset.sum Finset.univ (fun i : Fin S.card => l (wickSupportLabel S i)) :=
      (wickSupportLabel_sum S l).symm
    _ = Finset.sum Finset.univ (fun i : Fin S.card => d.blocksFun (Fin.cast hLen.symm i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact wickDegreesOfComposition_label S d hLen i
    _ = Finset.sum Finset.univ d.blocksFun := Equiv.sum_comp E d.blocksFun
    _ = m := d.sum_blocksFun

theorem wickDegreesOfComposition_admissible {m : Nat} (S : Finset J) (d : Composition m)
    (hLen : d.length = S.card) (hThree : forall i, 3 <= d.blocksFun i) :
    Membership.mem (wickScalarDegreeAssignments (J := J) m)
      (wickDegreesOfComposition S d hLen) := by
  rw [wickScalarDegreeAssignments_mem]
  refine And.intro (wickDegreesOfComposition_sum S d hLen) ?_
  intro j
  rw [wickDegreesOfComposition_apply]
  by_cases hj : Membership.mem S j
  case pos =>
    rw [dite_eq_left hj]
    exact Or.inr (hThree _)
  case neg =>
    rw [dite_eq_right hj]
    exact Or.inl rfl

theorem wickListOfFn_cast {m n : Nat} (h : m = n) (f : Fin n -> Nat) :
    List.ofFn (fun i : Fin m => f (Fin.cast h i)) = List.ofFn f := by
  cases h
  rfl

theorem wickDegreesOfComposition_reconstruct {m : Nat}
    (S : Finset J) (d : Composition m) (hLen : d.length = S.card)
    (hl : Membership.mem (wickScalarDegreeAssignments (J := J) m)
      (wickDegreesOfComposition S d hLen)) :
    wickCompositionOfAssignment m (wickDegreesOfComposition S d hLen) hl = d := by
  apply Composition.ext
  change List.ofFn (fun i : Fin (wickDegreesOfComposition S d hLen).support.card =>
    wickDegreesOfComposition S d hLen
      (wickSupportLabel (wickDegreesOfComposition S d hLen).support i)) = d.blocks
  rw [wickDegreesOfComposition_support]
  simp_rw [wickDegreesOfComposition_label]
  rw [wickListOfFn_cast, d.ofFn_blocksFun]

abbrev WickProfileOwner (e : Nat) :=
  {p : Prod (Finset J) (Composition (2 * e)) //
    Membership.mem (wickVertexProfiles e p.fst.card) p.snd}

def wickAssignmentToProfile (e : Nat)
    (l : {l : Finsupp J Nat //
      Membership.mem (wickScalarDegreeAssignments (J := J) (2 * e)) l}) :
    WickProfileOwner (J := J) e :=
  Subtype.mk (wickAssignmentOwner (2 * e) l)
    (wickCompositionOfAssignment_profile e l.val l.property)

theorem wickAssignmentToProfile_injective (e : Nat) :
    Function.Injective (wickAssignmentToProfile (J := J) e) := by
  intro a b h
  exact wickAssignmentOwner_injective (2 * e) (congrArg Subtype.val h)

theorem wickAssignmentToProfile_surjective (e : Nat) :
    Function.Surjective (wickAssignmentToProfile (J := J) e) := by
  intro p
  let S := p.val.fst
  let d := p.val.snd
  have hProfile := (wickVertexProfiles_mem e S.card d).mp p.property
  let l := wickDegreesOfComposition S d hProfile.1
  have hl : Membership.mem (wickScalarDegreeAssignments (J := J) (2 * e)) l :=
    wickDegreesOfComposition_admissible S d hProfile.1 hProfile.2
  refine Exists.intro (Subtype.mk l hl) ?_
  apply Subtype.ext
  apply Prod.ext
  case fst =>
    exact wickDegreesOfComposition_support S d hProfile.1
  case snd =>
    exact wickDegreesOfComposition_reconstruct S d hProfile.1 hl

def wickAssignmentProfileEquiv (e : Nat) :
    Equiv
      {l : Finsupp J Nat //
        Membership.mem (wickScalarDegreeAssignments (J := J) (2 * e)) l}
      (WickProfileOwner (J := J) e) :=
  Equiv.ofBijective (wickAssignmentToProfile e)
    (And.intro (wickAssignmentToProfile_injective e) (wickAssignmentToProfile_surjective e))

def wickProfileOwnerFinset (e : Nat) : Finset (Prod (Finset J) (Composition (2 * e))) :=
  (Finset.univ : Finset J).powerset.biUnion
    (fun S => (wickVertexProfiles e S.card).image (fun d => Prod.mk S d))

theorem wickProfileOwnerFinset_mem (e : Nat) (p : Prod (Finset J) (Composition (2 * e))) :
    Membership.mem (wickProfileOwnerFinset (J := J) e) p <->
      Membership.mem (wickVertexProfiles e p.fst.card) p.snd := by
  unfold wickProfileOwnerFinset
  constructor
  case mp =>
    intro hp
    have hS := Finset.mem_biUnion.mp hp
    let S := hS.choose
    have hImage := Finset.mem_image.mp hS.choose_spec.2
    let d := hImage.choose
    have hd := hImage.choose_spec.1
    have hPair := hImage.choose_spec.2
    have hFst : S = p.fst := congrArg Prod.fst hPair
    have hSnd : d = p.snd := congrArg Prod.snd hPair
    rw [<- hFst, <- hSnd]
    exact hd
  case mpr =>
    intro hp
    apply Finset.mem_biUnion.mpr
    have hSupport : Membership.mem Finset.univ.powerset p.fst :=
      Finset.mem_powerset.mpr (Finset.subset_univ p.fst)
    have hImage : Membership.mem
        ((wickVertexProfiles e p.fst.card).image (Prod.mk p.fst)) p :=
      Finset.mem_image.mpr
        (Exists.intro p.snd (And.intro hp (by cases p; rfl)))
    exact Exists.intro p.fst (And.intro hSupport hImage)

def wickProfileOwnerFinsetEquiv (e : Nat) :
    Equiv (WickProfileOwner (J := J) e)
      {p : Prod (Finset J) (Composition (2 * e)) //
        Membership.mem (wickProfileOwnerFinset (J := J) e) p} where
  toFun := fun p => Subtype.mk p.val ((wickProfileOwnerFinset_mem e p.val).mpr p.property)
  invFun := fun p => Subtype.mk p.val ((wickProfileOwnerFinset_mem e p.val).mp p.property)
  left_inv := by intro p; apply Subtype.ext; rfl
  right_inv := by intro p; apply Subtype.ext; rfl

def wickAssignmentOwnerFinsetEquiv (e : Nat) :
    Equiv
      {l : Finsupp J Nat //
        Membership.mem (wickScalarDegreeAssignments (J := J) (2 * e)) l}
      {p : Prod (Finset J) (Composition (2 * e)) //
        Membership.mem (wickProfileOwnerFinset (J := J) e) p} :=
  (wickAssignmentProfileEquiv e).trans (wickProfileOwnerFinsetEquiv e)

def wickScalarProfileContribution {m : Nat}
    (Y : J -> Complex) (p : Prod (Finset J) (Composition m)) : Complex :=
  if hLen : p.snd.length = p.fst.card then
    Finset.prod Finset.univ (fun i : Fin p.snd.length =>
      wickVertexCoefficient (p.snd.blocksFun i) *
        Y (wickSupportLabel p.fst (Fin.cast hLen i)) ^ p.snd.blocksFun i)
  else 0

theorem wickProdFin_cast {m n : Nat} (h : m = n) (f : Fin n -> Complex) :
    Finset.prod Finset.univ (fun i : Fin m => f (Fin.cast h i)) =
      Finset.prod Finset.univ f := by
  cases h
  rfl

theorem wickScalarProfileContribution_assignment (m : Nat) (Y : J -> Complex)
    (a : {l : Finsupp J Nat //
      Membership.mem (wickScalarDegreeAssignments (J := J) m) l}) :
    wickScalarProfileContribution Y (wickAssignmentOwner m a) =
      Finset.prod Finset.univ (fun j => wickVertexCoefficient (a.val j) * Y j ^ a.val j) := by
  dsimp only [wickAssignmentOwner, wickScalarProfileContribution]
  rw [dite_eq_left (wickCompositionOfAssignment_length m a.val a.property)]
  simp_rw [wickCompositionOfAssignment_blocksFun]
  rw [wickProdFin_cast (wickCompositionOfAssignment_length m a.val a.property)
    (fun i : Fin a.val.support.card =>
      wickVertexCoefficient (a.val (wickSupportLabel a.val.support i)) *
        Y (wickSupportLabel a.val.support i) ^
          a.val (wickSupportLabel a.val.support i)),
    wickSupportLabel_prod a.val.support
      (fun j => wickVertexCoefficient (a.val j) * Y j ^ a.val j)]
  apply Finset.prod_subset (Finset.subset_univ a.val.support)
  intro j hj hNot
  have hZero := Finsupp.notMem_support_iff.mp hNot
  rw [hZero, wickVertexCoefficient_initial.1, pow_zero, mul_one]

theorem wickVertexScalarProduct_coeff_profiles (Y : J -> Complex) (e : Nat) :
    PowerSeries.coeff (2 * e)
        (Finset.prod Finset.univ (fun j => wickVertexScalarSeries (Y j))) =
      Finset.sum (wickProfileOwnerFinset (J := J) e)
        (wickScalarProfileContribution Y) := by
  classical
  letI : Fintype {l : Finsupp J Nat //
      Membership.mem (wickScalarDegreeAssignments (J := J) (2 * e)) l} :=
    Finset.fintypeCoeSort (wickScalarDegreeAssignments (J := J) (2 * e))
  rw [wickVertexScalarProduct_coeff]
  have hReindex := Equiv.sum_comp (wickAssignmentOwnerFinsetEquiv (J := J) e)
    (fun p : {p : Prod (Finset J) (Composition (2 * e)) //
        Membership.mem (wickProfileOwnerFinset (J := J) e) p} =>
        wickScalarProfileContribution Y p.val)
  change Finset.sum Finset.univ
      (fun a => wickScalarProfileContribution Y (wickAssignmentOwner (2 * e) a)) =
    Finset.sum Finset.univ
      (fun p : {p : Prod (Finset J) (Composition (2 * e)) //
        Membership.mem (wickProfileOwnerFinset (J := J) e) p} =>
        wickScalarProfileContribution Y p.val) at hReindex
  calc
    _ = Finset.sum Finset.univ
        (fun a : {l : Finsupp J Nat //
          Membership.mem (wickScalarDegreeAssignments (J := J) (2 * e)) l} =>
          Finset.prod Finset.univ
            (fun j => wickVertexCoefficient (a.val j) * Y j ^ a.val j)) :=
      (Finset.sum_coe_sort
        (s := wickScalarDegreeAssignments (J := J) (2 * e))
        (f := fun l => Finset.prod Finset.univ
          (fun j => wickVertexCoefficient (l j) * Y j ^ l j))).symm
    _ = Finset.sum Finset.univ
        (fun a => wickScalarProfileContribution Y (wickAssignmentOwner (2 * e) a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (wickScalarProfileContribution_assignment (2 * e) Y a).symm
    _ = Finset.sum Finset.univ
        (fun p : {p : Prod (Finset J) (Composition (2 * e)) //
        Membership.mem (wickProfileOwnerFinset (J := J) e) p} =>
        wickScalarProfileContribution Y p.val) := hReindex
    _ = _ := Finset.sum_coe_sort
      (s := wickProfileOwnerFinset (J := J) e) (f := wickScalarProfileContribution Y)

end PrimeFactorOscillations
