/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRealFiniteFactors

/-! # Injective row and column restriction without a spectral loss -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota Kappa Lambda : Type*}
variable [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota]
variable [Fintype Kappa] [DecidableEq Kappa]
variable [Fintype Lambda] [DecidableEq Lambda]

def hamiltonianRowSelector (f : Iota -> Jota) : Matrix Iota Jota Real :=
  fun i j => if f i = j then 1 else 0

theorem hamiltonian_row_selector_gram (f : Iota -> Jota) (hf : Function.Injective f) :
    hamiltonianRowSelector f * (hamiltonianRowSelector f).transpose =
      (1 : Matrix Iota Iota Real) := by
  ext i j
  simp [Matrix.mul_apply, hamiltonianRowSelector, Matrix.transpose_apply,
    ite_mul, hf.eq_iff, eq_comm, Matrix.one_apply]

theorem hamiltonian_row_selector_norm (f : Iota -> Jota) (hf : Function.Injective f) :
    norm (hamiltonianRowSelector f) <= 1 := by
  let P := hamiltonianRowSelector f
  have hGram : P * P.transpose = (1 : Matrix Iota Iota Real) :=
    hamiltonian_row_selector_gram f hf
  have hConj : P.transpose.conjTranspose = P := by ext i j; rfl
  have hSquare := Matrix.l2_opNorm_conjTranspose_mul_self P.transpose
  rw [hConj, hGram, hamiltonian_real_transpose_norm] at hSquare
  have hIdentity : norm (1 : Matrix Iota Iota Real) <= 1 := by
    rw [<- Matrix.l2_opNorm_toEuclideanCLM]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    rw [map_one]
    change norm x <= 1 * norm x
    rw [one_mul]
  have hBound : norm P * norm P <= 1 := by
    rw [<- hSquare]
    exact hIdentity
  change norm P <= 1
  nlinarith only [hBound, norm_nonneg P]

theorem hamiltonian_row_selector_product
    (f : Iota -> Jota) (M : Matrix Jota Kappa Real) :
    hamiltonianRowSelector f * M = M.submatrix f id := by
  ext i j
  simp [Matrix.mul_apply, hamiltonianRowSelector, ite_mul]

theorem hamiltonian_column_selector_product
    (f : Iota -> Jota) (M : Matrix Kappa Jota Real) :
    M * (hamiltonianRowSelector f).transpose = M.submatrix id f := by
  ext i j
  simp [Matrix.mul_apply, hamiltonianRowSelector, Matrix.transpose_apply, mul_ite]

theorem hamiltonian_injective_rows_norm
    (f : Iota -> Jota) (hf : Function.Injective f) (M : Matrix Jota Kappa Real) :
    norm (M.submatrix f id) <= norm M := by
  rw [<- hamiltonian_row_selector_product f M]
  calc
    _ <= norm (hamiltonianRowSelector f) * norm M := Matrix.l2_opNorm_mul _ _
    _ <= 1 * norm M := mul_le_mul_of_nonneg_right
      (hamiltonian_row_selector_norm f hf) (norm_nonneg M)
    _ = _ := one_mul _

theorem hamiltonian_injective_columns_norm
    (f : Iota -> Jota) (hf : Function.Injective f) (M : Matrix Kappa Jota Real) :
    norm (M.submatrix id f) <= norm M := by
  rw [<- hamiltonian_column_selector_product f M]
  calc
    _ <= norm M * norm (hamiltonianRowSelector f).transpose := Matrix.l2_opNorm_mul _ _
    _ = norm M * norm (hamiltonianRowSelector f) := by
      rw [hamiltonian_real_transpose_norm]
    _ <= norm M * 1 := mul_le_mul_of_nonneg_left
      (hamiltonian_row_selector_norm f hf) (norm_nonneg M)
    _ = _ := mul_one _

theorem hamiltonian_injective_submatrix_norm
    (f : Iota -> Jota) (g : Lambda -> Kappa)
    (hf : Function.Injective f) (hg : Function.Injective g) (M : Matrix Jota Kappa Real) :
    norm (M.submatrix f g) <= norm M := by
  calc
    _ = norm ((M.submatrix f id).submatrix id g) := rfl
    _ <= norm (M.submatrix f id) := hamiltonian_injective_columns_norm g hg _
    _ <= _ := hamiltonian_injective_rows_norm f hf M

theorem hamiltonian_restricted_product
    (f g : Iota -> Jota) (U : Matrix Jota Kappa Real) (V : Matrix Kappa Jota Real) :
    (U * V).submatrix f g = U.submatrix f id * V.submatrix id g := by
  ext i j
  rfl

end PrimeFactorOscillations
