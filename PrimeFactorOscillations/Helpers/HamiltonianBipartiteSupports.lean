/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Sum
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteMinorPolynomial
import PrimeFactorOscillations.Helpers.HamiltonianBipartitePermanent

/-! # Actual independently selected bipartite supports

Both vertex supports and both complementary supports are transported
explicitly. Balanced determinant and permanent factors use the actual
rectangular minor enumerations; unbalanced determinant terms are exactly
zero. No equality of the selected row and column sets is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota R : Type*}
variable [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota] [CommRing R]

def hamiltonianDisjSumEquiv (S : Finset Iota) (U : Finset Jota) :
    Equiv (Sum S U) (S.disjSum U) := by
  classical
  exact {
    toFun := fun x => match x with
      | Sum.inl i => Subtype.mk (Sum.inl i.val) (Finset.inl_mem_disjSum.mpr i.property)
      | Sum.inr j => Subtype.mk (Sum.inr j.val) (Finset.inr_mem_disjSum.mpr j.property)
    invFun := fun x => match x with
      | Subtype.mk (Sum.inl i) hx => Sum.inl (Subtype.mk i (Finset.inl_mem_disjSum.mp hx))
      | Subtype.mk (Sum.inr j) hx => Sum.inr (Subtype.mk j (Finset.inr_mem_disjSum.mp hx))
    left_inv := by intro x; cases x <;> rfl
    right_inv := by
      intro x
      cases x with
      | mk x hx => cases x <;> rfl }

def hamiltonianDisjSumComplementEquiv (S : Finset Iota) (U : Finset Jota) :
    Equiv (Sum (Compl.compl S : Finset Iota) (Compl.compl U : Finset Jota))
      {x : Sum Iota Jota // Not (Membership.mem (S.disjSum U) x)} := by
  classical
  exact {
    toFun := fun x => match x with
      | Sum.inl i => Subtype.mk (Sum.inl i.val)
          (by simpa only [Finset.inl_mem_disjSum] using (Finset.mem_compl.mp i.property))
      | Sum.inr j => Subtype.mk (Sum.inr j.val)
          (by simpa only [Finset.inr_mem_disjSum] using (Finset.mem_compl.mp j.property))
    invFun := fun x => match x with
      | Subtype.mk (Sum.inl i) hx =>
          Sum.inl (Subtype.mk i (Finset.mem_compl.mpr
            (by simpa only [Finset.inl_mem_disjSum] using hx)))
      | Subtype.mk (Sum.inr j) hx =>
          Sum.inr (Subtype.mk j (Finset.mem_compl.mpr
            (by simpa only [Finset.inr_mem_disjSum] using hx)))
    left_inv := by intro x; cases x <;> rfl
    right_inv := by
      intro x
      cases x with
      | mk x hx => cases x <;> rfl }

theorem hamiltonianBipartiteMinor_reindex
    (T : Matrix Iota Jota R) (S : Finset Iota) (U : Finset Jota) :
    ((bipartiteLift T).submatrix
      (Subtype.val : S.disjSum U -> Sum Iota Jota)
      (Subtype.val : S.disjSum U -> Sum Iota Jota)).submatrix
        (hamiltonianDisjSumEquiv S U) (hamiltonianDisjSumEquiv S U) =
      bipartiteLift (T.submatrix (Subtype.val : S -> Iota) (Subtype.val : U -> Jota)) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;> rfl

theorem hamiltonianBipartiteComplement_reindex
    (T : Matrix Iota Jota R) (S : Finset Iota) (U : Finset Jota) :
    ((bipartiteLift T).submatrix
      (fun x : {x : Sum Iota Jota // Not (Membership.mem (S.disjSum U) x)} => x.val)
      (fun x : {x : Sum Iota Jota // Not (Membership.mem (S.disjSum U) x)} => x.val)).submatrix
        (hamiltonianDisjSumComplementEquiv S U) (hamiltonianDisjSumComplementEquiv S U) =
      bipartiteLift (T.submatrix
        (fun i : (Compl.compl S : Finset Iota) => (i.val : Iota))
        (fun i : (Compl.compl U : Finset Jota) => (i.val : Jota))) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;> rfl

theorem hamiltonianBipartite_reindex_left (T : Matrix Iota Jota R) (e : Equiv Jota Iota) :
    (bipartiteLift T).submatrix (Equiv.sumCongr e (Equiv.refl Jota))
        (Equiv.sumCongr e (Equiv.refl Jota)) =
      bipartiteLift (T.submatrix e id) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;> rfl

theorem hamiltonianBipartiteDet_of_equiv (T : Matrix Iota Jota R) (e : Equiv Jota Iota) :
    Matrix.det (bipartiteLift T) =
      (-1 : R) ^ Fintype.card Jota * Matrix.det (T.submatrix e id) ^ 2 := by
  classical
  have h := Matrix.det_submatrix_equiv_self (Equiv.sumCongr e (Equiv.refl Jota))
    (bipartiteLift T)
  rw [hamiltonianBipartite_reindex_left] at h
  exact h.symm.trans (hamiltonianBipartiteDet_square (T.submatrix e id))

theorem hamiltonianBipartitePermanent_of_equiv
    (T : Matrix Iota Jota R) (e : Equiv Jota Iota) :
    finitePermutationSum (bipartiteLift T) = finitePermutationSum (T.submatrix e id) ^ 2 := by
  classical
  have h := finitePermutationSum_reindex (Equiv.sumCongr e (Equiv.refl Jota)) (bipartiteLift T)
  rw [hamiltonianBipartite_reindex_left] at h
  exact h.symm.trans (finitePermutationSum_bipartiteLift (T.submatrix e id))

def rectangularMinorPermanent (T : Matrix Iota Iota R) (S U : Finset Iota) : R :=
  if h : S.card = U.card then
    finitePermutationSum (T.submatrix
      (fun i : U => (equalCardMinorEquiv S U h i).val)
      (Subtype.val : U -> Iota))
  else 0

theorem hamiltonianBipartite_principalMinor
    (T : Matrix Iota Iota R) (S U : Finset Iota) :
    principalMinorDet (bipartiteLift T) (S.disjSum U) =
      if S.card = U.card then
        (-1 : R) ^ U.card * rectangularMinorDet T S U ^ 2 else 0 := by
  classical
  let Q : Matrix S U R := T.submatrix (Subtype.val : S -> Iota) (Subtype.val : U -> Iota)
  have h := Matrix.det_submatrix_equiv_self (hamiltonianDisjSumEquiv S U)
    ((bipartiteLift T).submatrix (Subtype.val : S.disjSum U -> Sum Iota Iota)
      (Subtype.val : S.disjSum U -> Sum Iota Iota))
  rw [hamiltonianBipartiteMinor_reindex] at h
  change Matrix.det (bipartiteLift Q) = _ at h
  change Matrix.det ((bipartiteLift T).submatrix
    (Subtype.val : S.disjSum U -> Sum Iota Iota)
    (Subtype.val : S.disjSum U -> Sum Iota Iota)) = _
  rw [<- h]
  by_cases hCard : S.card = U.card
  next =>
    rw [if_pos hCard]
    let e : Equiv U S := equalCardMinorEquiv S U hCard
    have hSquare := hamiltonianBipartiteDet_of_equiv Q e
    rw [Fintype.card_coe] at hSquare
    rw [hSquare]
    unfold rectangularMinorDet
    rw [dite_eq_left hCard]
    rfl
  next =>
    rw [if_neg hCard]
    apply hamiltonianBipartiteDet_zero_of_unbalanced
    simpa only [Fintype.card_coe] using hCard

theorem hamiltonianBipartite_complementaryPermanent
    (T : Matrix Iota Iota R) (S U : Finset Iota) (hCard : S.card = U.card) :
    finitePermutationSum ((bipartiteLift T).submatrix
      (fun x : {x : Sum Iota Iota // Not (Membership.mem (S.disjSum U) x)} => x.val)
      (fun x : {x : Sum Iota Iota // Not (Membership.mem (S.disjSum U) x)} => x.val)) =
      rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) ^ 2 := by
  classical
  have hComplement : (Compl.compl S).card = (Compl.compl U).card := by
    simp only [Finset.card_compl, hCard]
  let Q := T.submatrix
    (fun i : (Compl.compl S : Finset Iota) => (i.val : Iota))
    (fun i : (Compl.compl U : Finset Iota) => (i.val : Iota))
  have h := finitePermutationSum_reindex (hamiltonianDisjSumComplementEquiv S U)
    ((bipartiteLift T).submatrix
      (fun x : {x : Sum Iota Iota // Not (Membership.mem (S.disjSum U) x)} => x.val)
      (fun x : {x : Sum Iota Iota // Not (Membership.mem (S.disjSum U) x)} => x.val))
  rw [hamiltonianBipartiteComplement_reindex] at h
  rw [<- h]
  let e : Equiv (Compl.compl U : Finset Iota) (Compl.compl S : Finset Iota) :=
    equalCardMinorEquiv (Compl.compl S) (Compl.compl U) hComplement
  have hSquare := hamiltonianBipartitePermanent_of_equiv Q e
  rw [hSquare]
  unfold rectangularMinorPermanent
  rw [dite_eq_left hComplement]
  rfl

end PrimeFactorOscillations
