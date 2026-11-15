/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import PrimeFactorOscillations.Helpers.HamiltonianBoundaryEquations

/-! # Exact principal inverse determinant identity on independent supports

The finite support and its complement are reindexed explicitly. The
signed Schur product is retained before taking determinants. Empty
removed or retained support is included.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianSupportPartitionEquiv (D : Finset Iota) :
    Equiv (Sum D (Compl.compl D : Finset Iota)) Iota where
  toFun := Sum.elim (fun d => d.val) (fun r => r.val)
  invFun := fun i =>
    if h : Membership.mem D i then Sum.inl (Subtype.mk i h)
    else Sum.inr (Subtype.mk i (Finset.mem_compl.mpr h))
  left_inv := by
    intro x
    cases x with
    | inl d =>
      change (if h : Membership.mem D d.val then Sum.inl (Subtype.mk d.val h)
        else Sum.inr (Subtype.mk d.val (Finset.mem_compl.mpr h))) = Sum.inl d
      rw [dite_eq_left d.property]
    | inr r =>
      change (if h : Membership.mem D r.val then Sum.inl (Subtype.mk r.val h)
        else Sum.inr (Subtype.mk r.val (Finset.mem_compl.mpr h))) = Sum.inr r
      rw [dite_eq_right (Finset.mem_compl.mp r.property)]
  right_inv := by
    intro i
    by_cases h : Membership.mem D i
    case pos => simp only [dite_eq_left h, Sum.elim_inl]
    case neg => simp only [dite_eq_right h, Sum.elim_inr]

theorem hamiltonian_det_schur_ring_inverse {Jota : Type*}
    [Fintype Jota] [DecidableEq Jota]
    (A : Matrix Iota Iota Real) (B : Matrix Iota Jota Real)
    (C : Matrix Jota Iota Real) (D : Matrix Jota Jota Real) (hA : IsUnit A) :
    Matrix.det (Matrix.fromBlocks A B C D) =
      Matrix.det A * Matrix.det (D - C * Ring.inverse A * B) := by
  have hCancel : Ring.inverse A * A = 1 := Ring.inverse_mul_cancel _ hA
  have hLower : C * Ring.inverse A * A = C := by
    rw [Matrix.mul_assoc, hCancel, Matrix.mul_one]
  have hFactor :
      Matrix.fromBlocks A B C D =
        Matrix.fromBlocks (1 : Matrix Iota Iota Real) 0 (C * Ring.inverse A) 1 *
          Matrix.fromBlocks A B 0 (D - C * Ring.inverse A * B) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, hLower, add_sub_cancel]
  rw [hFactor, Matrix.det_mul]
  simp

theorem hamiltonian_boundary_kernel_determinant
    (K : Matrix Iota Iota Real) (D : Finset Iota)
    (hUnit : IsUnit (K.submatrix (fun d : D => d.val) (fun d : D => d.val))) :
    Matrix.det K =
      Matrix.det (K.submatrix (fun d : D => d.val) (fun d : D => d.val)) *
        Matrix.det (hamiltonianBoundaryKernel K D) := by
  let e := hamiltonianSupportPartitionEquiv D
  have hBlock : K.submatrix e e = Matrix.fromBlocks
      (K.submatrix (fun d : D => d.val) (fun d : D => d.val))
      (K.submatrix (fun d : D => d.val)
        (fun r : (Compl.compl D : Finset Iota) => r.val))
      (K.submatrix (fun r : (Compl.compl D : Finset Iota) => r.val)
        (fun d : D => d.val))
      (K.submatrix (fun r : (Compl.compl D : Finset Iota) => r.val)
        (fun r : (Compl.compl D : Finset Iota) => r.val)) := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  calc
    _ = Matrix.det (K.submatrix e e) := (Matrix.det_submatrix_equiv_self e K).symm
    _ = _ := by
      rw [hBlock, hamiltonian_det_schur_ring_inverse _ _ _ _ hUnit]
      rfl

theorem hamiltonian_principal_inverse_complement_determinant
    (H K : Matrix Iota Iota Real) (D : Finset Iota) (hInverse : H * K = 1)
    (hUnit : IsUnit (K.submatrix (fun d : D => d.val) (fun d : D => d.val))) :
    Matrix.det (H.submatrix
      (fun r : (Compl.compl D : Finset Iota) => r.val)
      (fun r : (Compl.compl D : Finset Iota) => r.val)) / Matrix.det H =
        Matrix.det (K.submatrix (fun d : D => d.val) (fun d : D => d.val)) := by
  let rr := fun r : (Compl.compl D : Finset Iota) => (r.val : Iota)
  let rd := fun d : D => (d.val : Iota)
  let G := hamiltonianBoundaryKernel K D
  have hRR : (1 : Matrix Iota Iota Real).submatrix rr rr = 1 := by
    apply Matrix.ext
    intro i j
    simp only [rr, Matrix.submatrix_apply, Matrix.one_apply, Subtype.ext_iff]
  have hRD : (1 : Matrix Iota Iota Real).submatrix rr rd = 0 := by
    apply Matrix.ext
    intro i d
    have hne : Not (i.val = d.val) := by
      intro h
      have hm : Membership.mem D i.val := by rw [h]; exact d.property
      exact (Finset.mem_compl.mp i.property) hm
    simp only [rr, rd, Matrix.submatrix_apply, Matrix.one_apply, Matrix.zero_apply, ite_eq_right hne]
  have hRetained := hamiltonianBoundaryKernel_inverse_equation H K D hUnit
  rw [hInverse, hRR, hRD, Matrix.zero_mul, Matrix.zero_mul, sub_zero] at hRetained
  have hDetRetained : Matrix.det (H.submatrix rr rr) * Matrix.det G = 1 := by
    rw [<- Matrix.det_mul]
    change Matrix.det (H.submatrix rr rr * hamiltonianBoundaryKernel K D) = 1
    rw [hRetained, Matrix.det_one]
  have hDetFull : Matrix.det H * Matrix.det K = 1 := by
    rw [<- Matrix.det_mul, hInverse, Matrix.det_one]
  have hDetH : Not (Matrix.det H = 0) := by
    intro h
    rw [h, zero_mul] at hDetFull
    norm_num at hDetFull
  have hSchur := hamiltonian_boundary_kernel_determinant K D hUnit
  have hNumerator : Matrix.det (H.submatrix rr rr) =
      Matrix.det H * Matrix.det (K.submatrix rd rd) := by
    calc
      _ = Matrix.det (H.submatrix rr rr) * (Matrix.det H * Matrix.det K) := by
        rw [hDetFull, mul_one]
      _ = (Matrix.det H * Matrix.det (K.submatrix rd rd)) *
          (Matrix.det (H.submatrix rr rr) * Matrix.det G) := by rw [hSchur]; ring
      _ = _ := by rw [hDetRetained, mul_one]
  change Matrix.det (H.submatrix rr rr) / Matrix.det H = Matrix.det (K.submatrix rd rd)
  rw [hNumerator]
  field_simp

end PrimeFactorOscillations
