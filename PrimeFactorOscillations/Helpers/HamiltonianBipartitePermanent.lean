/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteDeterminant
import PrimeFactorOscillations.Helpers.HamiltonianPermanentSplitting

/-! # Actual bipartite complementary permanent factors

The two parts are represented by their actual finite vertex subsets.
Transport to the coordinate types is explicit. Exact zero-pattern splitting
then gives the diagonal block permanent, and row interchange gives the full
bipartite permanent square, without any independence assumption.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota R : Type*}
variable [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota] [CommRing R]

def hamiltonianLeftPart (Iota Jota : Type*) [Fintype Iota] [Fintype Jota] :
    Finset (Sum Iota Jota) := by
  classical
  exact Finset.univ.filter (fun x => match x with
    | Sum.inl _ => True
    | Sum.inr _ => False)

theorem hamiltonianLeftPart_mem_inl (i : Iota) :
    Membership.mem (hamiltonianLeftPart Iota Jota) (Sum.inl i) := by
  classical
  simp [hamiltonianLeftPart]

theorem hamiltonianLeftPart_notMem_inr (j : Jota) :
    Not (Membership.mem (hamiltonianLeftPart Iota Jota) (Sum.inr j)) := by
  classical
  simp [hamiltonianLeftPart]

def hamiltonianLeftPartEquiv :
    Equiv {x : Sum Iota Jota // Membership.mem (hamiltonianLeftPart Iota Jota) x} Iota := by
  classical
  exact {
    toFun := fun x => match x with
      | Subtype.mk (Sum.inl i) _ => i
      | Subtype.mk (Sum.inr j) hx => False.elim (hamiltonianLeftPart_notMem_inr j hx)
    invFun := fun i => Subtype.mk (Sum.inl i) (hamiltonianLeftPart_mem_inl i)
    left_inv := by
      intro x
      cases x with
      | mk x hx =>
        cases x with
        | inl i => rfl
        | inr j => exact False.elim (hamiltonianLeftPart_notMem_inr j hx)
    right_inv := fun _ => rfl }

def hamiltonianRightPartEquiv :
    Equiv {x : Sum Iota Jota // Not (Membership.mem (hamiltonianLeftPart Iota Jota) x)} Jota := by
  classical
  exact {
    toFun := fun x => match x with
      | Subtype.mk (Sum.inl i) hx => False.elim (hx (hamiltonianLeftPart_mem_inl i))
      | Subtype.mk (Sum.inr j) _ => j
    invFun := fun j => Subtype.mk (Sum.inr j) (hamiltonianLeftPart_notMem_inr j)
    left_inv := by
      intro x
      cases x with
      | mk x hx =>
        cases x with
        | inl i => exact False.elim (hx (hamiltonianLeftPart_mem_inl i))
        | inr j => rfl
    right_inv := fun _ => rfl }

theorem finitePermutationSum_fromBlocks_diagonal
    (A : Matrix Iota Iota R) (D : Matrix Jota Jota R) :
    finitePermutationSum (Matrix.fromBlocks A 0 0 D) =
      finitePermutationSum A * finitePermutationSum D := by
  classical
  let M : Matrix (Sum Iota Jota) (Sum Iota Jota) R := Matrix.fromBlocks A 0 0 D
  let S := hamiltonianLeftPart Iota Jota
  have hCross : forall i j,
      Not (Membership.mem S i <-> Membership.mem S j) -> M i j = 0 := by
    intro i j h
    cases i <;> cases j <;> simp_all [S, M, hamiltonianLeftPart, Matrix.fromBlocks]
  have hSplit := finitePermutationSum_zeroPattern M S hCross
  have hLeft :
      finitePermutationSum (M.submatrix
        (fun i : {x : Sum Iota Jota // Membership.mem S x} => i.val)
        (fun i : {x : Sum Iota Jota // Membership.mem S x} => i.val)) =
          finitePermutationSum A := by
    let e : Equiv {x : Sum Iota Jota // Membership.mem S x} Iota :=
      hamiltonianLeftPartEquiv
    let Q := M.submatrix
      (fun i : {x : Sum Iota Jota // Membership.mem S x} => i.val)
      (fun i : {x : Sum Iota Jota // Membership.mem S x} => i.val)
    have h := finitePermutationSum_reindex e.symm Q
    have hMatrix : Q.submatrix e.symm e.symm = A := by
      apply Matrix.ext
      intro i j
      rfl
    rw [hMatrix] at h
    exact h.symm
  have hRight :
      finitePermutationSum (M.submatrix
        (fun i : {x : Sum Iota Jota // Not (Membership.mem S x)} => i.val)
        (fun i : {x : Sum Iota Jota // Not (Membership.mem S x)} => i.val)) =
          finitePermutationSum D := by
    let e : Equiv {x : Sum Iota Jota // Not (Membership.mem S x)} Jota :=
      hamiltonianRightPartEquiv
    let Q := M.submatrix
      (fun i : {x : Sum Iota Jota // Not (Membership.mem S x)} => i.val)
      (fun i : {x : Sum Iota Jota // Not (Membership.mem S x)} => i.val)
    have h := finitePermutationSum_reindex e.symm Q
    have hMatrix : Q.submatrix e.symm e.symm = D := by
      apply Matrix.ext
      intro i j
      rfl
    rw [hMatrix] at h
    exact h.symm
  rw [hLeft, hRight] at hSplit
  exact hSplit

theorem finitePermutationSum_bipartiteLift (T : Matrix Iota Iota R) :
    finitePermutationSum (bipartiteLift T) = finitePermutationSum T ^ 2 := by
  classical
  have h := finitePermutationSum_rowPerm (bipartiteLift T) (Equiv.sumComm Iota Iota)
  have hMatrix : (bipartiteLift T).submatrix (Equiv.sumComm Iota Iota) id =
      Matrix.fromBlocks T.transpose 0 0 T := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  rw [hMatrix, finitePermutationSum_fromBlocks_diagonal, finitePermutationSum_transpose] at h
  rw [pow_two]
  exact h.symm

end PrimeFactorOscillations
