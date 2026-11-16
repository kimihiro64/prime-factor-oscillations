/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBlockCovariance

/-! # Lossless finite reindexing and bipartite block extraction -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Kappa : Type*} [Fintype Iota] [Fintype Kappa]
  [DecidableEq Iota] [DecidableEq Kappa]

theorem hamiltonian_sum_reindex (e : Equiv Kappa Iota) (f : Iota -> Real) :
    Finset.sum Finset.univ (fun j => f (e j)) = Finset.sum Finset.univ f := by
  apply Finset.sum_bij (fun j _ => e j)
  . intro j hj
    exact Finset.mem_univ _
  . intro i hi j hj h
    exact e.injective h
  . intro i hi
    exact Exists.intro (e.symm i) (Exists.intro (Finset.mem_univ _) (e.apply_symm_apply i))
  . intro j hj
    rfl

def hamiltonianReindexVector (e : Equiv Kappa Iota)
    (x : EuclideanSpace Real Iota) : EuclideanSpace Real Kappa :=
  WithLp.toLp 2 (fun j => x.ofLp (e j))

theorem hamiltonian_reindex_vector_norm (e : Equiv Kappa Iota)
    (x : EuclideanSpace Real Iota) : norm (hamiltonianReindexVector e x) = norm x := by
  have hs : norm (hamiltonianReindexVector e x) ^ 2 = norm x ^ 2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, hamiltonianReindexVector,
      WithLp.ofLp_toLp] using hamiltonian_sum_reindex e (fun i => x.ofLp i ^ 2)
  nlinarith only [hs, norm_nonneg x, norm_nonneg (hamiltonianReindexVector e x)]

theorem hamiltonian_reindex_matrix_norm_le (e : Equiv Kappa Iota)
    (M : Matrix Iota Iota Real) : norm (M.submatrix e e) <= norm M := by
  let opM := (@Matrix.toEuclideanCLM Real Iota _ _ _) M
  let opN := (@Matrix.toEuclideanCLM Real Kappa _ _ _) (M.submatrix e e)
  have hOp : norm opN <= norm M := by
    apply ContinuousLinearMap.opNorm_le_bound opN (norm_nonneg M)
    intro x
    let y := hamiltonianReindexVector e.symm x
    have hxy : opN x = hamiltonianReindexVector e (opM y) := by
      change WithLp.toLp 2 ((M.submatrix e e).mulVec x.ofLp) =
        WithLp.toLp 2 (fun i => M.mulVec y.ofLp (e i))
      congr 1
      funext i
      change Finset.sum Finset.univ (fun j => M (e i) (e j) * x.ofLp j) =
        Finset.sum Finset.univ (fun k => M (e i) k * x.ofLp (e.symm k))
      simpa only [e.symm_apply_apply] using
        hamiltonian_sum_reindex e (fun k => M (e i) k * x.ofLp (e.symm k))
    rw [hxy, hamiltonian_reindex_vector_norm]
    have h := opM.le_opNorm y
    rw [Matrix.l2_opNorm_toEuclideanCLM] at h
    simpa only [y, hamiltonian_reindex_vector_norm] using h
  rwa [Matrix.l2_opNorm_toEuclideanCLM] at hOp

theorem hamiltonian_reindex_matrix_norm (e : Equiv Kappa Iota)
    (M : Matrix Iota Iota Real) : norm (M.submatrix e e) = norm M := by
  apply le_antisymm (hamiltonian_reindex_matrix_norm_le e M)
  have h := hamiltonian_reindex_matrix_norm_le e.symm (M.submatrix e e)
  have heq : (M.submatrix e e).submatrix e.symm e.symm = M := by
    ext i j
    simp only [Matrix.submatrix_apply, e.apply_symm_apply]
  rwa [heq] at h

theorem hamiltonian_block_norm_le_lift (B : Matrix Iota Iota Real) :
    norm B <= norm (bipartiteLift B) := by
  let opB := (@Matrix.toEuclideanCLM Real Iota _ _ _) B
  let opP := (@Matrix.toEuclideanCLM Real (Sum Iota Iota) _ _ _) (bipartiteLift B)
  have hOp : norm opB <= norm (bipartiteLift B) := by
    apply ContinuousLinearMap.opNorm_le_bound opB (norm_nonneg _)
    intro x
    let v : EuclideanSpace Real (Sum Iota Iota) :=
      WithLp.toLp 2 (Sum.elim (fun _ => 0) x.ofLp)
    have hv : norm v = norm x := by
      have hs : norm v ^ 2 = norm x ^ 2 := by
        simp [EuclideanSpace.real_norm_sq_eq, v, Fintype.sum_sum_type]
      nlinarith only [hs, norm_nonneg v, norm_nonneg x]
    have hp : norm (opP v) = norm (opB x) := by
      have hs : norm (opP v) ^ 2 = norm (opB x) ^ 2 := by
        simp only [EuclideanSpace.real_norm_sq_eq]
        change Finset.sum Finset.univ
          (fun k => ((bipartiteLift B).mulVec v.ofLp k) ^ 2) = _
        simp [bipartiteLift, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
          Matrix.fromBlocks, v, opB]
      nlinarith only [hs, norm_nonneg (opP v), norm_nonneg (opB x)]
    have h := opP.le_opNorm v
    rw [Matrix.l2_opNorm_toEuclideanCLM, hv, hp] at h
    exact h
  rwa [Matrix.l2_opNorm_toEuclideanCLM] at hOp

theorem hamiltonian_bipartite_lift_norm (B : Matrix Iota Iota Real) :
    norm (bipartiteLift B) = norm B :=
  le_antisymm (bipartiteLift_l2_norm_le B) (hamiltonian_block_norm_le_lift B)

end PrimeFactorOscillations
