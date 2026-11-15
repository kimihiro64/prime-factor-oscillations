/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianWickSeriesCoefficients

/-! # Exact ownership of scalar Wick degree assignments

The complete finite product coefficient is restricted only by exact zero
coefficients. Every retained assignment has its actual support and a
canonical composition, without imposing an order on the vertex type.
This is the finite ownership step in the actual Gaussian Taylor readout.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {J : Type*} [Fintype J] [DecidableEq J]

def wickVertexScalarSeries (z : Complex) : PowerSeries Complex :=
  PowerSeries.mk (fun k => wickVertexCoefficient k * z ^ k)

theorem wickVertexScalarSeries_coeff (z : Complex) (k : Nat) :
    PowerSeries.coeff k (wickVertexScalarSeries z) =
      wickVertexCoefficient k * z ^ k := by
  simp only [wickVertexScalarSeries, PowerSeries.coeff_mk]

def wickScalarDegreeAssignments (m : Nat) : Finset (Finsupp J Nat) :=
  (Finset.finsuppAntidiag (Finset.univ : Finset J) m).filter
    (fun l => forall j, Or (l j = 0) (3 <= l j))

theorem wickScalarDegreeAssignments_mem (m : Nat) (l : Finsupp J Nat) :
    Membership.mem (wickScalarDegreeAssignments (J := J) m) l <->
      And (Finset.sum Finset.univ (fun j => l j) = m)
        (forall j, Or (l j = 0) (3 <= l j)) := by
  simp only [wickScalarDegreeAssignments, Finset.mem_filter,
    Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]

theorem wickScalarAssignment_zero (Y : J -> Complex) (l : Finsupp J Nat)
    (hNot : Not (forall j, Or (l j = 0) (3 <= l j))) :
    Finset.prod Finset.univ (fun j =>
      wickVertexCoefficient (l j) * Y j ^ l j) = 0 := by
  have hBad := not_forall.mp hNot
  let j := hBad.choose
  have hJ := hBad.choose_spec
  have hValue : Or (l j = 1) (l j = 2) := by
    change Not (Or (l j = 0) (3 <= l j)) at hJ
    omega
  have hZero : wickVertexCoefficient (l j) = 0 := by
    cases hValue with
    | inl hOne => rw [hOne, wickVertexCoefficient_initial.2.1]
    | inr hTwo => rw [hTwo, wickVertexCoefficient_initial.2.2]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hZero, zero_mul]

theorem wickVertexScalarProduct_coeff (Y : J -> Complex) (m : Nat) :
    PowerSeries.coeff m (Finset.prod Finset.univ (fun j => wickVertexScalarSeries (Y j))) =
      Finset.sum (wickScalarDegreeAssignments (J := J) m) (fun l =>
        Finset.prod Finset.univ (fun j => wickVertexCoefficient (l j) * Y j ^ l j)) := by
  rw [PowerSeries.coeff_prod]
  simp only [wickVertexScalarSeries_coeff]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro l hl hNot
  apply wickScalarAssignment_zero Y l
  intro hAll
  exact hNot (Finset.mem_filter.mpr (And.intro hl hAll))

def wickSupportIndexEquiv (S : Finset J) :
    Equiv (Fin S.card) {j : J // Membership.mem S j} := by
  let hCard : S.card = Fintype.card {j : J // Membership.mem S j} := by
    simp only [Fintype.card_coe]
  let E := Fintype.equivFin {j : J // Membership.mem S j}
  exact
    { toFun := fun i => E.symm (Fin.cast hCard i)
      invFun := fun j => Fin.cast hCard.symm (E j)
      left_inv := by
        intro i
        change Fin.cast hCard.symm (E (E.symm (Fin.cast hCard i))) = i
        rw [Equiv.apply_symm_apply]
        apply Fin.ext
        rfl
      right_inv := by
        intro j
        change E.symm (Fin.cast hCard (Fin.cast hCard.symm (E j))) = j
        have hFin : Fin.cast hCard (Fin.cast hCard.symm (E j)) = E j := by
          apply Fin.ext
          rfl
        rw [hFin, Equiv.symm_apply_apply] }

theorem wickSupportIndexEquiv_val (S : Finset J) (i : Fin S.card) :
    (wickSupportIndexEquiv S i).val = wickSupportLabel S i := by
  rfl

theorem wickSupportLabel_mem (S : Finset J) (i : Fin S.card) :
    Membership.mem S (wickSupportLabel S i) := by
  rw [<- wickSupportIndexEquiv_val]
  exact (wickSupportIndexEquiv S i).property

theorem wickSupportLabel_injective (S : Finset J) :
    Function.Injective (wickSupportLabel S) := by
  intro i j h
  apply (wickSupportIndexEquiv S).injective
  apply Subtype.ext
  simpa only [wickSupportIndexEquiv_val] using h

theorem wickSupportLabel_surjective (S : Finset J) (j : J)
    (hj : Membership.mem S j) :
    Exists (fun i : Fin S.card => wickSupportLabel S i = j) := by
  let a : {j : J // Membership.mem S j} := Subtype.mk j hj
  refine Exists.intro ((wickSupportIndexEquiv S).symm a) ?_
  have h := congrArg Subtype.val ((wickSupportIndexEquiv S).apply_symm_apply a)
  simpa only [wickSupportIndexEquiv_val] using h

theorem wickSupportLabel_sum (S : Finset J) (f : J -> Nat) :
    Finset.sum Finset.univ (fun i : Fin S.card => f (wickSupportLabel S i)) =
      Finset.sum S f := by
  calc
    _ = Finset.sum Finset.univ
        (fun i : Fin S.card => f (wickSupportIndexEquiv S i).val) := by rfl
    _ = Finset.sum Finset.univ (fun j : {j : J // Membership.mem S j} => f j.val) :=
      Equiv.sum_comp (wickSupportIndexEquiv S) (fun j => f j.val)
    _ = _ := Finset.sum_coe_sort (f := f) (s := S)

theorem wickSupportLabel_prod (S : Finset J) (f : J -> Complex) :
    Finset.prod Finset.univ (fun i : Fin S.card => f (wickSupportLabel S i)) =
      Finset.prod S f := by
  calc
    _ = Finset.prod Finset.univ
        (fun i : Fin S.card => f (wickSupportIndexEquiv S i).val) := by rfl
    _ = Finset.prod Finset.univ (fun j : {j : J // Membership.mem S j} => f j.val) :=
      Equiv.prod_comp (wickSupportIndexEquiv S) (fun j => f j.val)
    _ = _ := Finset.prod_coe_sort (f := f) (s := S)

theorem wickScalarDegreeAssignments_support_sum (m : Nat) (l : Finsupp J Nat)
    (hl : Membership.mem (wickScalarDegreeAssignments (J := J) m) l) :
    Finset.sum l.support (fun j => l j) = m := by
  have hSum := ((wickScalarDegreeAssignments_mem m l).mp hl).1
  rw [<- hSum]
  apply Finset.sum_subset (Finset.subset_univ l.support)
  intro j hj hNot
  exact Finsupp.notMem_support_iff.mp hNot

theorem wickScalarDegreeAssignments_support_degree (m : Nat) (l : Finsupp J Nat)
    (hl : Membership.mem (wickScalarDegreeAssignments (J := J) m) l)
    (j : J) (hj : Membership.mem l.support j) :
    3 <= l j := by
  have hAllowed := ((wickScalarDegreeAssignments_mem m l).mp hl).2 j
  have hNonzero := Finsupp.mem_support_iff.mp hj
  cases hAllowed with
  | inl hZero => exact False.elim (hNonzero hZero)
  | inr hThree => exact hThree

def wickCompositionOfAssignment (m : Nat) (l : Finsupp J Nat)
    (hl : Membership.mem (wickScalarDegreeAssignments (J := J) m) l) :
    Composition m where
  blocks := List.ofFn (fun i : Fin l.support.card => l (wickSupportLabel l.support i))
  blocks_pos := by
    intro a ha
    have hWitness := List.mem_ofFn.mp ha
    let i := hWitness.choose
    have hValue := hWitness.choose_spec
    have hThree := wickScalarDegreeAssignments_support_degree m l hl
      (wickSupportLabel l.support i) (wickSupportLabel_mem l.support i)
    change l (wickSupportLabel l.support i) = a at hValue
    omega
  blocks_sum := by
    rw [List.sum_ofFn, wickSupportLabel_sum]
    exact wickScalarDegreeAssignments_support_sum m l hl

theorem wickCompositionOfAssignment_length (m : Nat) (l : Finsupp J Nat)
    (hl : Membership.mem (wickScalarDegreeAssignments (J := J) m) l) :
    (wickCompositionOfAssignment m l hl).length = l.support.card := by
  simp only [wickCompositionOfAssignment, Composition.length, List.length_ofFn]

theorem wickCompositionOfAssignment_blocksFun (m : Nat) (l : Finsupp J Nat)
    (hl : Membership.mem (wickScalarDegreeAssignments (J := J) m) l)
    (i : Fin (wickCompositionOfAssignment m l hl).length) :
    (wickCompositionOfAssignment m l hl).blocksFun i =
      l (wickSupportLabel l.support
        (Fin.cast (wickCompositionOfAssignment_length m l hl) i)) := by
  exact List.get_ofFn
    (fun k : Fin l.support.card => l (wickSupportLabel l.support k)) i

theorem wickCompositionOfAssignment_profile (e : Nat) (l : Finsupp J Nat)
    (hl : Membership.mem (wickScalarDegreeAssignments (J := J) (2 * e)) l) :
    Membership.mem (wickVertexProfiles e l.support.card)
      (wickCompositionOfAssignment (2 * e) l hl) := by
  rw [wickVertexProfiles_mem]
  refine And.intro (wickCompositionOfAssignment_length (2 * e) l hl) ?_
  intro i
  rw [wickCompositionOfAssignment_blocksFun]
  exact wickScalarDegreeAssignments_support_degree (2 * e) l hl _
    (wickSupportLabel_mem l.support _)

theorem wickCompositionOfAssignment_unique (m : Nat) (l k : Finsupp J Nat)
    (hl : Membership.mem (wickScalarDegreeAssignments (J := J) m) l)
    (hk : Membership.mem (wickScalarDegreeAssignments (J := J) m) k)
    (hSupport : l.support = k.support)
    (hComposition : wickCompositionOfAssignment m l hl = wickCompositionOfAssignment m k hk) :
    l = k := by
  have hBlocks := congrArg Composition.blocks hComposition
  change List.ofFn (fun i : Fin l.support.card => l (wickSupportLabel l.support i)) =
    List.ofFn (fun i : Fin k.support.card => k (wickSupportLabel k.support i)) at hBlocks
  rw [hSupport] at hBlocks
  have hFunctions := List.ofFn_inj.mp hBlocks
  apply Finsupp.ext
  intro j
  by_cases hMem : Membership.mem k.support j
  case pos =>
    have hIndex := wickSupportLabel_surjective k.support j hMem
    have h := congrFun hFunctions hIndex.choose
    rw [hIndex.choose_spec] at h
    exact h
  case neg =>
    have hNotL : Not (Membership.mem l.support j) := by
      rw [hSupport]
      exact hMem
    rw [Finsupp.notMem_support_iff.mp hNotL, Finsupp.notMem_support_iff.mp hMem]

def wickAssignmentOwner (m : Nat)
    (l : {l : Finsupp J Nat // Membership.mem (wickScalarDegreeAssignments (J := J) m) l}) :
    Prod (Finset J) (Composition m) :=
  Prod.mk l.val.support (wickCompositionOfAssignment m l.val l.property)

theorem wickAssignmentOwner_injective (m : Nat) :
    Function.Injective (wickAssignmentOwner (J := J) m) := by
  intro a b h
  apply Subtype.ext
  have hSupport : a.val.support = b.val.support := congrArg Prod.fst h
  have hComposition :
      wickCompositionOfAssignment m a.val a.property =
        wickCompositionOfAssignment m b.val b.property := congrArg Prod.snd h
  exact wickCompositionOfAssignment_unique m a.val b.val
    a.property b.property hSupport hComposition

theorem wickScalarDegreeAssignments_support_card (e : Nat) (l : Finsupp J Nat)
    (hl : Membership.mem (wickScalarDegreeAssignments (J := J) (2 * e)) l) :
    3 * l.support.card <= 2 * e :=
  wickVertexProfiles_support_bound e l.support.card _
    (wickCompositionOfAssignment_profile e l hl)

end PrimeFactorOscillations
