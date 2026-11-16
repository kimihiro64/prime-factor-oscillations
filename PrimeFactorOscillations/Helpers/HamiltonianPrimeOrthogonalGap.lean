/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCuts

/-! # The actual constant/parity orthogonal operator consumer -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_constant_parity_mulVec (n : Nat) (x : Fin n -> Real) (i : Fin n) :
    (hamiltonianRealConstantParityMatrix n).mulVec x i =
      (Finset.univ.sum x - (-1 : Real) ^ (i.val + 1) *
        Finset.univ.sum (fun j => (-1 : Real) ^ (j.val + 1) * x j)) / (n : Real) := by
  have hPoint (j : Fin n) :
      hamiltonianRealConstantParityMatrix n i j * x j =
        (x j - (-1 : Real) ^ (i.val + 1) * ((-1 : Real) ^ (j.val + 1) * x j)) /
          (n : Real) := by
    simp only [hamiltonianRealConstantParityMatrix, pow_add]
    ring
  unfold Matrix.mulVec dotProduct
  simp_rw [hPoint, <- Finset.sum_div, Finset.sum_sub_distrib, <- Finset.mul_sum]

theorem hamiltonian_constant_parity_orthogonal_bound (n : Nat)
    (M : Matrix (Fin n) (Fin n) Real) (rho : Real)
    (hNorm : norm (M - hamiltonianRealConstantParityMatrix n) <= rho)
    (x : EuclideanSpace Real (Fin n))
    (hSum : Finset.univ.sum x.ofLp = 0)
    (hParity : Finset.univ.sum (fun i => (-1 : Real) ^ (i.val + 1) * x.ofLp i) = 0) :
    norm (WithLp.toLp 2 (M.mulVec x.ofLp) : EuclideanSpace Real (Fin n)) <= rho * norm x := by
  have hZero : (hamiltonianRealConstantParityMatrix n).mulVec x.ofLp = 0 := by
    funext i
    rw [hamiltonian_constant_parity_mulVec, hSum, hParity, mul_zero, sub_zero, zero_div]
    rfl
  have hId : (M - hamiltonianRealConstantParityMatrix n).mulVec x.ofLp = M.mulVec x.ofLp := by
    rw [Matrix.sub_mulVec, hZero, sub_zero]
  have h := Matrix.l2_opNorm_mulVec (M - hamiltonianRealConstantParityMatrix n) x
  rw [hId] at h
  exact h.trans (mul_le_mul_of_nonneg_right hNorm (norm_nonneg x))

end PrimeFactorOscillations.LPF
