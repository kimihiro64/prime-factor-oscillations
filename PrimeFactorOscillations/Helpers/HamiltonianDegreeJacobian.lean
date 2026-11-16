/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompatiblePerturbation
import PrimeFactorOscillations.Helpers.HamiltonianRepairInverse

/-! # The actual bipartite degree Jacobian and its compatible inverse

The degree diagonal is retained. Its parity kernel is exact even before
normalization. Both row and column support corrections are coupled in
the perturbation and in the resulting inverse identity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianBipartiteDegree (T : Matrix Iota Iota Real) : Sum Iota Iota -> Real :=
  fun i => match i with
    | Sum.inl i => Finset.univ.sum (fun j => T i j)
    | Sum.inr j => Finset.univ.sum (fun i => T i j)

def hamiltonianDegreeJacobian (T : Matrix Iota Iota Real) :
    Matrix (Sum Iota Iota) (Sum Iota Iota) Real :=
  Matrix.diagonal (hamiltonianBipartiteDegree T) + bipartiteLift T

theorem hamiltonian_bipartite_degree_row (T : Matrix Iota Iota Real)
    (i : Sum Iota Iota) :
    Finset.univ.sum (fun j => bipartiteLift T i j) = hamiltonianBipartiteDegree T i := by
  cases i <;> simp [hamiltonianBipartiteDegree, bipartiteLift, Matrix.fromBlocks,
    Matrix.transpose_apply, Fintype.sum_sum_type]

theorem hamiltonian_degree_jacobian_parity (T : Matrix Iota Iota Real) (q : Real) :
    hamiltonianParityProjection (Iota := Iota) q * hamiltonianDegreeJacobian T = 0 := by
  unfold hamiltonianDegreeJacobian
  rw [mul_add]
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_diagonal]
  cases i <;> cases j <;>
    simp [Matrix.add_apply, Matrix.mul_diagonal, Matrix.mul_apply,
      Fintype.sum_sum_type, hamiltonianParityProjection, hamiltonianParitySign,
      hamiltonianBipartiteDegree, bipartiteLift, Matrix.fromBlocks,
      Matrix.transpose_apply, <- Finset.mul_sum, <- Finset.sum_mul] <;> ring

theorem hamiltonian_stochastic_degree_jacobian (U : Matrix Iota Iota Real)
    (hRow : forall i, Finset.univ.sum (fun j => U i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => U i j) = 1) :
    hamiltonianDegreeJacobian U = 1 + bipartiteLift U := by
  have hDegree : hamiltonianBipartiteDegree U = 1 := by
    funext i
    cases i <;> simp [hamiltonianBipartiteDegree, hRow, hCol]
  unfold hamiltonianDegreeJacobian
  rw [hDegree]
  congr 1

theorem hamiltonian_degree_jacobian_row_error (T U : Matrix Iota Iota Real)
    (eps r : Real)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps)
    (hDiffRow : forall i, Finset.univ.sum (fun j => abs (T i j - U i j)) <= r)
    (hDiffCol : forall j, Finset.univ.sum (fun i => abs (T i j - U i j)) <= r)
    (i : Sum Iota Iota) :
    hamiltonianRowMass (hamiltonianDegreeJacobian T - (1 + bipartiteLift U)) i <= eps + r := by
  have hDiag : Matrix.diagonal (hamiltonianBipartiteDegree T - 1) =
      Matrix.diagonal (hamiltonianBipartiteDegree T) -
        (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.diagonal_apply, Matrix.sub_apply, Matrix.one_apply, hij]
  have hE : hamiltonianDegreeJacobian T - (1 + bipartiteLift U) =
      Matrix.diagonal (hamiltonianBipartiteDegree T - 1) +
        (bipartiteLift T - bipartiteLift U) := by
    rw [hDiag]
    unfold hamiltonianDegreeJacobian
    abel
  have hDegree : abs (hamiltonianBipartiteDegree T i - 1) <= eps := by
    cases i with
    | inl i => exact hRow i
    | inr j => exact hCol j
  have hDiagonal : hamiltonianRowMass (Matrix.diagonal (hamiltonianBipartiteDegree T - 1)) i <= eps := by
    simpa [hamiltonianRowMass, Matrix.diagonal_apply, abs_ite] using hDegree
  have hLift : hamiltonianRowMass (bipartiteLift T - bipartiteLift U) i <= r := by
    cases i with
    | inl i =>
      simpa [hamiltonianRowMass, bipartiteLift, Matrix.fromBlocks,
        Matrix.sub_apply, Matrix.transpose_apply, Fintype.sum_sum_type] using hDiffRow i
    | inr j =>
      simpa [hamiltonianRowMass, bipartiteLift, Matrix.fromBlocks,
        Matrix.sub_apply, Matrix.transpose_apply, Fintype.sum_sum_type] using hDiffCol j
  rw [hE]
  exact (hamiltonian_row_mass_add _ _ i).trans (add_le_add hDiagonal hLift)

theorem hamiltonian_degree_jacobian_inverse_from_reference
    (T U : Matrix Iota Iota Real)
    (K : Matrix (Sum Iota Iota) (Sum Iota Iota) Real)
    (q eps r g : Real) (hEps : 0 <= eps) (hr : 0 <= r) (hg : 0 <= g)
    (hURow : forall i, Finset.univ.sum (fun j => U i j) = 1)
    (hUCol : forall j, Finset.univ.sum (fun i => U i j) = 1)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps)
    (hDiffRow : forall i, Finset.univ.sum (fun j => abs (T i j - U i j)) <= r)
    (hDiffCol : forall j, Finset.univ.sum (fun i => abs (T i j - U i j)) <= r)
    (hRight : (1 + bipartiteLift U) * K = 1 - hamiltonianParityProjection q)
    (hK : forall i, hamiltonianRowMass K i <= g)
    (hSmall : (eps + r) * g <= 1 / 2) :
    exists G : Matrix (Sum Iota Iota) (Sum Iota Iota) Real,
      hamiltonianDegreeJacobian T * G = 1 - hamiltonianParityProjection q /\
        forall i, hamiltonianRowMass G i <= 2 * g := by
  let J0 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real := 1 + bipartiteLift U
  let E := hamiltonianDegreeJacobian T - J0
  have hE : forall i, hamiltonianRowMass E i <= eps + r :=
    hamiltonian_degree_jacobian_row_error T U eps r hRow hCol hDiffRow hDiffCol
  have hCompatibility : hamiltonianParityProjection q * E = 0 := by
    dsimp only [E]
    rw [mul_sub, hamiltonian_degree_jacobian_parity]
    have hJ0 : J0 = hamiltonianDegreeJacobian U :=
      (hamiltonian_stochastic_degree_jacobian U hURow hUCol).symm
    rw [hJ0, hamiltonian_degree_jacobian_parity, sub_self]
  have h := hamiltonian_compatible_inverse_perturbation J0 K E (hamiltonianParityProjection q)
    g (eps + r) hg (add_nonneg hEps hr) hK hE hSmall hRight hCompatibility
  have hSum : J0 + E = hamiltonianDegreeJacobian T := by dsimp only [E]; abel
  rw [hSum] at h
  exact Exists.intro (hamiltonianCompatibleInverse K E) h

end PrimeFactorOscillations
