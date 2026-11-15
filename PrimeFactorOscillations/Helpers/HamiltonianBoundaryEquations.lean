/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBoundarySchur

/-! # Exact boundary equations before the nonlinear repair

The support partition and the Schur inverse equation retain all matrix
products. No term of the signed equation is replaced by a norm.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_sum_support_partition (f : Iota -> Real) (D : Finset Iota) :
    Finset.sum Finset.univ f =
      Finset.sum Finset.univ (fun d : D => f d.val) +
        Finset.sum Finset.univ (fun r : (Compl.compl D : Finset Iota) => f r.val) := by
  rw [Finset.sum_coe_sort, Finset.sum_coe_sort]
  exact (Finset.sum_add_sum_compl D f).symm

theorem hamiltonian_matrix_support_partition {Rows Cols : Type*}
    (H K : Matrix Iota Iota Real) (D : Finset Iota)
    (f : Rows -> Iota) (g : Cols -> Iota) :
    (H * K).submatrix f g =
      H.submatrix f (fun d : D => d.val) * K.submatrix (fun d : D => d.val) g +
        H.submatrix f (fun r : (Compl.compl D : Finset Iota) => r.val) *
          K.submatrix (fun r : (Compl.compl D : Finset Iota) => r.val) g := by
  apply Matrix.ext
  intro i j
  change Finset.sum Finset.univ (fun k => H (f i) k * K k (g j)) =
    Finset.sum Finset.univ (fun d : D => H (f i) d.val * K d.val (g j)) +
      Finset.sum Finset.univ (fun r : (Compl.compl D : Finset Iota) =>
        H (f i) r.val * K r.val (g j))
  exact hamiltonian_sum_support_partition _ D

theorem hamiltonianBoundaryKernel_inverse_equation
    (H K : Matrix Iota Iota Real) (D : Finset Iota)
    (hUnit : IsUnit (K.submatrix (fun d : D => d.val) (fun d : D => d.val))) :
    H.submatrix (fun r : (Compl.compl D : Finset Iota) => r.val) (fun r => r.val) *
        hamiltonianBoundaryKernel K D =
      (H * K).submatrix (fun r : (Compl.compl D : Finset Iota) => r.val) (fun r => r.val) -
        (H * K).submatrix (fun r : (Compl.compl D : Finset Iota) => r.val)
          (fun d : D => d.val) *
            Ring.inverse (K.submatrix (fun d : D => d.val) (fun d : D => d.val)) *
              K.submatrix (fun d : D => d.val)
                (fun r : (Compl.compl D : Finset Iota) => r.val) := by
  let rd : D -> Iota := fun d => d.val
  let rr := fun r : (Compl.compl D : Finset Iota) => (r.val : Iota)
  let A := K.submatrix rd rd
  let B := K.submatrix rd rr
  let C := K.submatrix rr rd
  let E := K.submatrix rr rr
  let L := H.submatrix rr rd
  let M := H.submatrix rr rr
  let J := Ring.inverse A
  have hRR : (H * K).submatrix rr rr = L * B + M * E :=
    hamiltonian_matrix_support_partition H K D rr rr
  have hRD : (H * K).submatrix rr rd = L * A + M * C :=
    hamiltonian_matrix_support_partition H K D rr rd
  have hAJ : A * J = 1 := Ring.mul_inverse_cancel _ hUnit
  have hCancel : (L * A) * J * B = L * B := by
    rw [Matrix.mul_assoc L A J, hAJ, Matrix.mul_one]
  change M * (E - C * J * B) = (H * K).submatrix rr rr -
    (H * K).submatrix rr rd * J * B
  rw [hRR, hRD]
  simp only [Matrix.mul_sub, Matrix.add_mul]
  rw [hCancel]
  simp only [Matrix.mul_assoc]
  abel

end PrimeFactorOscillations
