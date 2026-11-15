/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRepairedSquareExists

/-! # Exact permanent transport for the same positive physical repair -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem finitePermutationSum_diagonal_scale {K : Type*} [CommSemiring K]
    (M : Matrix Iota Iota K) (left right : Iota -> K) :
    finitePermutationSum (fun i j => left i * M i j * right j) =
      (Finset.univ.prod left) * (Finset.univ.prod right) * finitePermutationSum M := by
  unfold finitePermutationSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma hs
  simp only [Finset.prod_mul_distrib]
  rw [Equiv.prod_comp sigma left]
  ring

theorem hamiltonian_repaired_permanent_transport
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hPos : forall i, 0 < 1 + z i) :
    finitePermutationSum (hamiltonianRepairedSquareKernel T S U hCard z) =
      Real.exp (Finset.univ.sum (fun i => Real.log (1 + z i))) *
        rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) := by
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  let J : Finset Iota := Compl.compl U
  let e := hamiltonianRepairedSquareEquiv S U hCard
  let left := fun i : J => 1 + z (e (Sum.inl i))
  let right := fun i : J => 1 + z (e (Sum.inr i))
  let M : Matrix J J Real := fun i j => T (hamiltonianComplementRowEquiv S U hCard i).val j.val
  have hComplement : (Compl.compl S).card = (Compl.compl U).card := by
    simp only [Finset.card_compl, hCard]
  have hBase : finitePermutationSum M =
      rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) := by
    unfold rectangularMinorPermanent
    rw [dite_eq_left hComplement]
    rfl
  have hProduct : (Finset.univ.prod left) * (Finset.univ.prod right) =
      Real.exp (Finset.univ.sum (fun i : R => Real.log (1 + z i))) := by
    calc
      _ = Finset.univ.prod (fun i : Sum J J => 1 + z (e i)) := by
        rw [Fintype.prod_sum_type]
      _ = Finset.univ.prod (fun i : R => 1 + z i) :=
        Equiv.prod_comp e (fun i : R => 1 + z i)
      _ = _ := by
        rw [Real.exp_sum]
        apply Finset.prod_congr rfl
        intro i hi
        exact (Real.exp_log (hPos i)).symm
  change finitePermutationSum (fun i j => left i * M i j * right j) = _
  rw [finitePermutationSum_diagonal_scale, hProduct, hBase]

end PrimeFactorOscillations
