/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicLeadingTerm
import PrimeFactorOscillations.Helpers.HamiltonianLiuIdentity
import PrimeFactorOscillations.Helpers.HamiltonianMinorRelativeUniform

/-! # The actual signed aperiodic Liu residual

The principal complementary permanent uses the same maintained
rectangular-minor convention as the uniform comparison theorem.
Every support and the full ratio-minus-one subtraction are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianComplementSubtypeEquiv (S : Finset Iota) :
    Equiv (Compl.compl S : Finset Iota) {x : Iota // Not (Membership.mem S x)} := {
  toFun := fun x => Subtype.mk x.val (Finset.mem_compl.mp x.property)
  invFun := fun x => Subtype.mk x.val (Finset.mem_compl.mpr x.property)
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl }

theorem hamiltonian_rectangular_principal_permanent
    (T : Matrix Iota Iota Real) (S : Finset Iota) :
    rectangularMinorPermanent T S S =
      finitePermutationSum (T.submatrix (Subtype.val : S -> Iota) (Subtype.val : S -> Iota)) := by
  unfold rectangularMinorPermanent
  rw [dite_eq_left rfl]
  let e : Equiv.Perm S := equalCardMinorEquiv S S rfl
  change finitePermutationSum
      ((T.submatrix (Subtype.val : S -> Iota) (Subtype.val : S -> Iota)).submatrix e id) = _
  exact finitePermutationSum_rowPerm _ e

theorem hamiltonian_principal_complementary_permanent
    (T : Matrix Iota Iota Real) (S : Finset Iota) :
    finitePermutationSum (T.submatrix
      (fun x : {x : Iota // Not (Membership.mem S x)} => x.val)
      (fun x : {x : Iota // Not (Membership.mem S x)} => x.val)) =
        rectangularMinorPermanent T (Compl.compl S) (Compl.compl S) := by
  let M := T.submatrix
    (fun x : {x : Iota // Not (Membership.mem S x)} => x.val)
    (fun x : {x : Iota // Not (Membership.mem S x)} => x.val)
  have h := finitePermutationSum_reindex (hamiltonianComplementSubtypeEquiv S) M
  have hMatrix : M.submatrix (hamiltonianComplementSubtypeEquiv S)
      (hamiltonianComplementSubtypeEquiv S) =
      T.submatrix (fun i : (Compl.compl S : Finset Iota) => (i.val : Iota))
        (fun i : (Compl.compl S : Finset Iota) => (i.val : Iota)) := rfl
  rw [hMatrix] at h
  exact h.symm.trans (hamiltonian_rectangular_principal_permanent T (Compl.compl S)).symm

def hamiltonianAperiodicMinorRatio
    (T : Matrix Iota Iota Real) (S : Finset Iota) : Real :=
  rectangularMinorPermanent T (Compl.compl S) (Compl.compl S) / weightedPermutationSum T

theorem hamiltonian_aperiodic_liu_ratio (T : Matrix Iota Iota Real) :
    (Fintype.card Iota : Real) * hamiltonianCycleSum T / weightedPermutationSum T =
      -Finset.univ.sum (fun S : Finset Iota =>
        (S.card : Real) * principalMinorDet T S * (-1 : Real) ^ S.card *
          hamiltonianAperiodicMinorRatio T S) := by
  rw [<- hamiltonianLiuIdentity T]
  unfold hamiltonianLiuSum
  rw [neg_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  rw [hamiltonian_principal_complementary_permanent T S]
  unfold principalMinorDet hamiltonianAperiodicMinorRatio
  ring

theorem stochastic_aperiodic_signed_residual
    (T : Matrix Iota Iota Real) (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    (Fintype.card Iota : Real) * hamiltonianCycleSum T / weightedPermutationSum T -
        Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) =
      -Finset.univ.sum (fun S : Finset Iota =>
        (S.card : Real) * principalMinorDet T S * (-1 : Real) ^ S.card *
          (hamiltonianAperiodicMinorRatio T S - 1)) := by
  let w : Finset Iota -> Real := fun S =>
    (S.card : Real) * principalMinorDet T S * (-1 : Real) ^ S.card
  have hLeading : -Finset.univ.sum w =
      Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) :=
    stochastic_signed_principal_minor_signal T q hq hRow hCol
  calc
    _ = -Finset.univ.sum (fun S => w S * hamiltonianAperiodicMinorRatio T S) -
        (-Finset.univ.sum w) := by
      rw [hamiltonian_aperiodic_liu_ratio, hLeading]
    _ = -Finset.univ.sum (fun S => w S * hamiltonianAperiodicMinorRatio T S - w S) := by
      rw [Finset.sum_sub_distrib]
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      dsimp only [w]
      ring

end PrimeFactorOscillations
