/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRepairedSquareStochastic

/-! # The actual square repair preserves the Euclidean spectral gap -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_bipartite_l2_norm_eq (B : Matrix Iota Iota Real) :
    norm (bipartiteLift B) = norm B := by
  let L := bipartiteLift B
  have hBlock : (L.conjTranspose * L).submatrix Sum.inr Sum.inr = B.conjTranspose * B := by
    apply Matrix.ext
    intro i j
    simp [L, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
      bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply, Fintype.sum_sum_type]
  have hCompression := hamiltonian_l2_injective_submatrix_le
    (L.conjTranspose * L) Sum.inr Sum.inr_injective
  rw [hBlock, Matrix.l2_opNorm_conjTranspose_mul_self,
    Matrix.l2_opNorm_conjTranspose_mul_self] at hCompression
  have hLower : norm B <= norm L := by
    nlinarith only [hCompression, norm_nonneg B, norm_nonneg L]
  exact le_antisymm (bipartiteLift_l2_norm_le B) hLower

variable [Nonempty Iota]

theorem stochastic_repaired_square_gap
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * (a / (1 - rho)) ^ 3 * q <= 1 / 10000)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hZ : norm z <= 20 * (U.card : Real) * a * q / (1 - rho)) :
    norm (centeredKernel (hamiltonianRepairedSquareKernel T S U hCard z)
      (q / (1 - (U.card : Real) * q))) <= 1 - (1 - rho) / 2 := by
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  let e := hamiltonianRepairedSquareEquiv S U hCard
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
    bipartiteLift (centeredKernel T q)
  let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let qNew := q / (1 - (U.card : Real) * q)
  let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
    (hamiltonianRetainedCrossMask S U) z q qNew
  have hGap : norm (HR + E - 1) <= 1 - (1 - rho) / 2 :=
    (stochastic_retained_scaling_gap T S U q a rho hq ha hNonneg hUpper
      hNorm hRho hSmall z hZ).2
  have hTransport := hamiltonian_repaired_centered_reindex T S U hCard z q qNew
  have hReindex := hamiltonian_l2_reindex_norm (HR + E - 1) e
  change norm ((HR + E - 1).submatrix e e) = norm (HR + E - 1) at hReindex
  rw [hTransport, hamiltonian_bipartite_l2_norm_eq] at hReindex
  exact le_trans (le_of_eq hReindex) hGap

end PrimeFactorOscillations
