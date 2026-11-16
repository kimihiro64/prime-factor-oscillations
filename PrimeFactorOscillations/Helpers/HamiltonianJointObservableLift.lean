/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import PrimeFactorOscillations.Helpers.HamiltonianScaledCrossMass
import PrimeFactorOscillations.Helpers.HamiltonianSchurBudget

/-! # One linear matrix packet for the spectrum and two row observables -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianTwoObservableMatrix (S1 S2 : Finset Iota) (M : Matrix Iota Iota Real) :
    Matrix (Sum Iota (Sum Iota Iota)) (Sum Iota (Sum Iota Iota)) Real :=
  Matrix.fromBlocks M 0 0
    (Matrix.fromBlocks
      (Matrix.diagonal (fun i => S1.sum (fun j => M i j))) 0 0
      (Matrix.diagonal (fun i => S2.sum (fun j => M i j))))

def hamiltonianTwoObservableLift (S1 S2 : Finset Iota) :
    LinearMap (RingHom.id Real) (Matrix Iota Iota Real)
      (Matrix (Sum Iota (Sum Iota Iota)) (Sum Iota (Sum Iota Iota)) Real) where
  toFun M := hamiltonianTwoObservableMatrix S1 S2 M
  map_add' A B := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      by_cases hij : i = j <;>
      simp [hamiltonianTwoObservableMatrix, Matrix.fromBlocks, Matrix.diagonal,
        hij, Finset.sum_add_distrib]
  map_smul' r M := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      by_cases hij : i = j <;>
      simp [hamiltonianTwoObservableMatrix, Matrix.fromBlocks, Matrix.diagonal,
        hij, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem hamiltonian_two_observable_symmetric
    (S1 S2 : Finset Iota) (M : Matrix Iota Iota Real)
    (hSym : forall i j, M i j = M j i) :
    forall i j, hamiltonianTwoObservableMatrix S1 S2 M i j =
      hamiltonianTwoObservableMatrix S1 S2 M j i := by
  intro i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    by_cases hij : i = j <;>
    simp [hamiltonianTwoObservableMatrix, Matrix.fromBlocks, Matrix.diagonal,
      hij, eq_comm, hSym]

theorem hamiltonian_two_observable_hermitian
    (S1 S2 : Finset Iota) (M : Matrix Iota Iota Real) (hM : M.IsHermitian) :
    (hamiltonianTwoObservableMatrix S1 S2 M).IsHermitian := by
  have hSym (i j : Iota) : M i j = M j i := by
    change M.conjTranspose = M at hM
    have h := congrArg (fun A : Matrix Iota Iota Real => A i j) hM
    change M j i = M i j at h
    exact h.symm
  change (hamiltonianTwoObservableMatrix S1 S2 M).conjTranspose =
    hamiltonianTwoObservableMatrix S1 S2 M
  ext i j
  change hamiltonianTwoObservableMatrix S1 S2 M j i =
    hamiltonianTwoObservableMatrix S1 S2 M i j
  exact (hamiltonian_two_observable_symmetric S1 S2 M hSym i j).symm

theorem hamiltonian_two_observable_norm_from_rows
    (S1 S2 : Finset Iota) (M : Matrix Iota Iota Real)
    (hSym : forall i j, M i j = M j i) (r : Real) (hr : 0 <= r)
    (hRows : forall i, Finset.univ.sum (fun j => abs (M i j)) <= r) :
    norm (hamiltonianTwoObservableMatrix S1 S2 M) <= r := by
  have hCols (j : Iota) : Finset.univ.sum (fun i => abs (M i j)) <= r := by
    calc
      _ = Finset.univ.sum (fun i => abs (M j i)) :=
        Finset.sum_congr rfl (fun i _ => congrArg abs (hSym i j))
      _ <= r := hRows j
  have hObs1 := hamiltonian_absolute_mass_subset_observables M r hRows hCols S1
  have hObs2 := hamiltonian_absolute_mass_subset_observables M r hRows hCols S2
  apply hamiltonian_symmetric_row_budget _
    (hamiltonian_two_observable_symmetric S1 S2 M hSym) r hr
  intro i
  rcases i with i | i | i
  . simpa [hamiltonianTwoObservableMatrix, Matrix.fromBlocks,
      Fintype.sum_sum_type, Real.norm_eq_abs] using hRows i
  . simpa [hamiltonianTwoObservableMatrix, Matrix.fromBlocks, Matrix.diagonal,
      Fintype.sum_sum_type, Real.norm_eq_abs, apply_ite] using hObs1.1 i
  . simpa [hamiltonianTwoObservableMatrix, Matrix.fromBlocks, Matrix.diagonal,
      Fintype.sum_sum_type, Real.norm_eq_abs, apply_ite] using hObs2.1 i

theorem hamiltonian_two_observable_spectral_block
    (S1 S2 : Finset Iota) (M : Matrix Iota Iota Real) :
    (hamiltonianTwoObservableMatrix S1 S2 M).submatrix Sum.inl Sum.inl = M := rfl

theorem hamiltonian_two_observable_first_diagonal
    (S1 S2 : Finset Iota) (M : Matrix Iota Iota Real) (i : Iota) :
    hamiltonianTwoObservableMatrix S1 S2 M (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i)) =
      S1.sum (fun j => M i j) := by
  simp [hamiltonianTwoObservableMatrix, Matrix.fromBlocks]

theorem hamiltonian_two_observable_second_diagonal
    (S1 S2 : Finset Iota) (M : Matrix Iota Iota Real) (i : Iota) :
    hamiltonianTwoObservableMatrix S1 S2 M (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i)) =
      S2.sum (fun j => M i j) := by
  simp [hamiltonianTwoObservableMatrix, Matrix.fromBlocks]

end PrimeFactorOscillations
