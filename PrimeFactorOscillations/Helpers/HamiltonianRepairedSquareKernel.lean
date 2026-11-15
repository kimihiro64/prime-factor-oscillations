/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteSupports
import PrimeFactorOscillations.Helpers.HamiltonianStochasticRetainedGap

/-! # The actual repaired square kernel on independent complements

The two complements are identified by their proved equal cardinality.
All retained coordinates, both scaling multipliers and the shifted
reference are transported explicitly.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianComplementRowEquiv (S U : Finset Iota) (hCard : S.card = U.card) :
    Equiv (Compl.compl U : Finset Iota) (Compl.compl S : Finset Iota) := by
  have hComplement : (Compl.compl S).card = (Compl.compl U).card := by
    simp only [Finset.card_compl, hCard]
  exact equalCardMinorEquiv (Compl.compl S) (Compl.compl U) hComplement

def hamiltonianRetainedComplementEquiv (S U : Finset Iota) :
    Equiv (Sum (Compl.compl S : Finset Iota) (Compl.compl U : Finset Iota))
      (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) := by
  let e : Equiv {x : Sum Iota Iota // Not (Membership.mem (S.disjSum U) x)}
      (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) := {
    toFun := fun x => Subtype.mk x.val (Finset.mem_compl.mpr x.property)
    invFun := fun x => Subtype.mk x.val (Finset.mem_compl.mp x.property)
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl }
  exact (hamiltonianDisjSumComplementEquiv S U).trans e

def hamiltonianRepairedSquareEquiv (S U : Finset Iota) (hCard : S.card = U.card) :
    Equiv (Sum (Compl.compl U : Finset Iota) (Compl.compl U : Finset Iota))
      (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) :=
  (Equiv.sumCongr (hamiltonianComplementRowEquiv S U hCard)
    (Equiv.refl (Compl.compl U : Finset Iota))).trans (hamiltonianRetainedComplementEquiv S U)

theorem hamiltonianRepairedSquareEquiv_inl_val (S U : Finset Iota) (hCard : S.card = U.card)
    (i : (Compl.compl U : Finset Iota)) :
    (hamiltonianRepairedSquareEquiv S U hCard (Sum.inl i)).val =
      Sum.inl (hamiltonianComplementRowEquiv S U hCard i).val := by
  rfl

theorem hamiltonianRepairedSquareEquiv_inr_val (S U : Finset Iota) (hCard : S.card = U.card)
    (j : (Compl.compl U : Finset Iota)) :
    (hamiltonianRepairedSquareEquiv S U hCard (Sum.inr j)).val = Sum.inr j.val := by
  rfl

def hamiltonianRepairedSquareKernel (T : Matrix Iota Iota Real)
    (S U : Finset Iota) (hCard : S.card = U.card)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real) :
    Matrix (Compl.compl U : Finset Iota) (Compl.compl U : Finset Iota) Real :=
  fun i j =>
    (1 + z (hamiltonianRepairedSquareEquiv S U hCard (Sum.inl i))) *
      T (hamiltonianComplementRowEquiv S U hCard i).val j.val *
        (1 + z (hamiltonianRepairedSquareEquiv S U hCard (Sum.inr j)))

theorem hamiltonian_repaired_scaled_bipartite_reindex (T : Matrix Iota Iota Real)
    (S U : Finset Iota) (hCard : S.card = U.card)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real) :
    let e := hamiltonianRepairedSquareEquiv S U hCard
    (Matrix.diagonal (1 + z) * hamiltonianRetainedKernel T S U * Matrix.diagonal (1 + z)).submatrix e e =
      bipartiteLift (hamiltonianRepairedSquareKernel T S U hCard z) := by
  dsimp only
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [hamiltonianRepairedSquareKernel, Matrix.submatrix_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul, hamiltonianRetainedKernel, bipartiteLift, Matrix.fromBlocks,
      Matrix.transpose_apply, Matrix.transpose, hamiltonianRepairedSquareEquiv_inl_val,
      hamiltonianRepairedSquareEquiv_inr_val] <;> ring

theorem hamiltonian_repaired_cross_mask_reindex (S U : Finset Iota) (hCard : S.card = U.card) :
    let e := hamiltonianRepairedSquareEquiv S U hCard
    (hamiltonianRetainedCrossMask S U).submatrix e e =
      bipartiteLift (fun _ _ : (Compl.compl U : Finset Iota) => (1 : Real)) := by
  dsimp only
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [Matrix.submatrix_apply, hamiltonianRetainedCrossMask, bipartiteLift, Matrix.fromBlocks,
      Matrix.transpose_apply, Matrix.transpose, hamiltonianRepairedSquareEquiv_inl_val,
      hamiltonianRepairedSquareEquiv_inr_val]

theorem hamiltonian_repaired_centered_reindex (T : Matrix Iota Iota Real)
    (S U : Finset Iota) (hCard : S.card = U.card)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (q qNew : Real) :
    let D := S.disjSum U
    let R : Finset (Sum Iota Iota) := Compl.compl D
    let e := hamiltonianRepairedSquareEquiv S U hCard
    let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
      bipartiteLift (centeredKernel T q)
    let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew
    (HR + E - 1).submatrix e e =
      bipartiteLift (centeredKernel (hamiltonianRepairedSquareKernel T S U hCard z) qNew) := by
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let rr := fun i : R => (i.val : Sum Iota Iota)
  let e := hamiltonianRepairedSquareEquiv S U hCard
  let P := hamiltonianRetainedKernel T S U
  let C := hamiltonianRetainedCrossMask S U
  let V := Matrix.diagonal (1 + z) * P * Matrix.diagonal (1 + z)
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
    bipartiteLift (centeredKernel T q)
  let HR := H.submatrix rr rr
  let E := hamiltonianScalingPerturbation P C z q qNew
  have hOne : (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real).submatrix rr rr = 1 := by
    apply Matrix.ext
    intro i j
    simp only [rr, Matrix.submatrix_apply, Matrix.one_apply, Subtype.ext_iff]
  have hInit : HR = 1 + (bipartiteLift (centeredKernel T q)).submatrix rr rr := by
    calc
      _ = (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real).submatrix rr rr +
          (bipartiteLift (centeredKernel T q)).submatrix rr rr := by rfl
      _ = _ := by rw [hOne]
  have hHR : HR = 1 + P - HSMul.hSMul q C := by
    rw [hamiltonian_retained_centered_kernel T S U q] at hInit
    simpa only [add_sub_assoc] using hInit
  have hRaw : HR + E - 1 = V - HSMul.hSMul qNew C := by
    change HR + (V - P + HSMul.hSMul (q - qNew) C) - 1 = V - HSMul.hSMul qNew C
    rw [hHR, sub_smul]
    abel
  have hV : V.submatrix e e = bipartiteLift (hamiltonianRepairedSquareKernel T S U hCard z) :=
    hamiltonian_repaired_scaled_bipartite_reindex T S U hCard z
  have hC : C.submatrix e e =
      bipartiteLift (fun _ _ : (Compl.compl U : Finset Iota) => (1 : Real)) :=
    hamiltonian_repaired_cross_mask_reindex S U hCard
  have hTransport := congrArg (fun A : Matrix R R Real => A.submatrix e e) hRaw
  change (HR + E - 1).submatrix e e = V.submatrix e e - HSMul.hSMul qNew (C.submatrix e e) at hTransport
  rw [hV, hC] at hTransport
  have hCentered :
      bipartiteLift (centeredKernel (hamiltonianRepairedSquareKernel T S U hCard z) qNew) =
        bipartiteLift (hamiltonianRepairedSquareKernel T S U hCard z) -
          HSMul.hSMul qNew (bipartiteLift (fun _ _ : (Compl.compl U : Finset Iota) => (1 : Real))) := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply, Matrix.transpose,
        centeredKernel, averagingKernel, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  change (HR + E - 1).submatrix e e = _
  rw [hCentered]
  exact hTransport

end PrimeFactorOscillations
