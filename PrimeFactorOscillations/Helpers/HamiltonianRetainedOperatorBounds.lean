/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianTraceBounds

/-! # Euclidean operator bounds for the actual retained kernel

Coordinate restriction is a contraction, including empty retained types.
The dimension-times-entry bound is used only for the explicit scaling
perturbation, after all signed main terms have already been retained.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_l2_entry_budget (M : Matrix Iota Iota Real) (c : Real)
    (hc : 0 <= c) (hEntry : forall i j, abs (M i j) <= c) :
    norm M <= (Fintype.card Iota : Real) * c := by
  let m : Real := Fintype.card Iota
  let op := (@Matrix.toEuclideanCLM Real Iota _ _ _) M
  have hm : 0 <= m := Nat.cast_nonneg _
  have hRow (i : Iota) : Finset.sum Finset.univ (fun j => M i j ^ 2) <= m * c ^ 2 := by
    calc
      _ <= Finset.sum Finset.univ (fun _ : Iota => c ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        have h := mul_le_mul (hEntry i j) (hEntry i j) (abs_nonneg _) hc
        simpa only [<- pow_two, sq_abs] using h
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]
  have hOp : norm op <= m * c := by
    apply ContinuousLinearMap.opNorm_le_bound op (mul_nonneg hm hc)
    intro x
    let y := op x
    have hEach (i : Iota) : y.ofLp i ^ 2 <= (m * c ^ 2) * norm x ^ 2 := by
      have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) (fun j => x.ofLp j)
      have hFirst : y.ofLp i ^ 2 <=
          (Finset.sum Finset.univ (fun j => M i j ^ 2)) * norm x ^ 2 := by
        change (Finset.sum Finset.univ (fun j => M i j * x.ofLp j)) ^ 2 <= _
        rw [EuclideanSpace.real_norm_sq_eq]
        exact hCS
      exact le_trans hFirst (mul_le_mul_of_nonneg_right (hRow i) (sq_nonneg (norm x)))
    have hSquare : norm y ^ 2 <= (m * c * norm x) ^ 2 := by
      calc
        _ = Finset.sum Finset.univ (fun i => y.ofLp i ^ 2) := by rw [EuclideanSpace.real_norm_sq_eq]
        _ <= Finset.sum Finset.univ (fun _ : Iota => (m * c ^ 2) * norm x ^ 2) :=
          Finset.sum_le_sum (fun i _ => hEach i)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]; ring
    have hPositive : 0 <= m * c * norm x := mul_nonneg (mul_nonneg hm hc) (norm_nonneg x)
    nlinarith only [hSquare, hPositive, norm_nonneg y]
  have hNorm : norm op = norm M := Matrix.l2_opNorm_toEuclideanCLM M
  rw [hNorm] at hOp
  exact hOp

variable {Jota : Type*} [Fintype Jota] [DecidableEq Jota]

theorem hamiltonian_l2_injective_submatrix_le
    (M : Matrix Iota Iota Real) (f : Jota -> Iota) (hInjective : Function.Injective f) :
    norm (M.submatrix f f) <= norm M := by
  let F : Matrix Iota Jota Real := (1 : Matrix Iota Iota Real).submatrix id f
  have hOrth : F.transpose * F = (1 : Matrix Jota Jota Real) := by
    apply Matrix.ext
    intro i j
    simp [F, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
      Matrix.one_apply, hInjective.eq_iff]
  have hCompression : M.submatrix f f = F.transpose * M * F := by
    apply Matrix.ext
    intro i j
    simp [F, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.one_apply]
  have hRealTranspose : F.conjTranspose = F.transpose := by
    apply Matrix.ext
    intro i j
    rfl
  have hOne : norm (1 : Matrix Jota Jota Real) <= 1 := by
    rw [<- Matrix.l2_opNorm_toEuclideanCLM]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    rw [map_one]
    change norm x <= 1 * norm x
    rw [one_mul]
  have hFNormSquare : norm F * norm F <= 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self F
    rw [hRealTranspose, hOrth] at h
    rw [<- h]
    exact hOne
  have hFNorm : norm F <= 1 := by nlinarith only [hFNormSquare, norm_nonneg F]
  have hTransposeNorm : norm F.transpose = norm F := by
    simpa only [hRealTranspose] using Matrix.l2_opNorm_conjTranspose F
  have hFTNorm : norm F.transpose <= 1 := le_trans (le_of_eq hTransposeNorm) hFNorm
  rw [hCompression]
  calc
    _ <= norm (F.transpose * M) * norm F := Matrix.l2_opNorm_mul _ _
    _ <= (norm F.transpose * norm M) * norm F :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul F.transpose M) (norm_nonneg F)
    _ <= norm M * 1 :=
      mul_le_mul (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hFTNorm (norm_nonneg M))
        hFNorm (norm_nonneg F) (norm_nonneg M)
    _ = norm M := mul_one _

theorem hamiltonian_l2_reindex_norm
    (M : Matrix Iota Iota Real) (e : Equiv Jota Iota) :
    norm (M.submatrix e e) = norm M := by
  refine le_antisymm (hamiltonian_l2_injective_submatrix_le M e e.injective) ?_
  have h := hamiltonian_l2_injective_submatrix_le (M.submatrix e e) e.symm e.symm.injective
  have hBack : (M.submatrix e e).submatrix e.symm e.symm = M := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  rw [hBack] at h
  exact h

end PrimeFactorOscillations
