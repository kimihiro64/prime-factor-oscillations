/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Matrix.Spectrum
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteEigenvalues
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorNormalization

/-! # Actual nontrivial prime-factor eigenvalues and the native Hermitian spectrum -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_real_hermitian_eigenvalue_test
    {Iota : Type*} [Fintype Iota] [DecidableEq Iota]
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (a b rho : Real)
    (hTest : forall (lambda : Real) (x : Iota -> Real),
      Exists (fun j => Not (x j = 0)) ->
      (forall j, M.mulVec x j = lambda * x j) ->
      Not (lambda = a) -> Not (lambda = b) -> abs lambda <= rho)
    (i : Iota) (ha : Not (hM.eigenvalues i = a)) (hb : Not (hM.eigenvalues i = b)) :
    abs (hM.eigenvalues i) <= rho := by
  let v := hM.eigenvectorBasis i
  have hv : norm v = 1 := hM.eigenvectorBasis.orthonormal.1 i
  have hX : Exists (fun j => Not (v.ofLp j = 0)) := by
    by_contra h
    push Not at h
    have hs : norm v ^ 2 = 0 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp_rw [h]
      simp
    rw [hv] at hs
    norm_num at hs
  have hEigen : forall j, M.mulVec v.ofLp j = hM.eigenvalues i * v.ofLp j := by
    intro j
    have h := congrArg (fun f : Iota -> Real => f j) (hM.mulVec_eigenvectorBasis i)
    exact h
  exact hTest (hM.eigenvalues i) v.ofLp hX hEigen ha hb

namespace LPF

def hamiltonianPrimeRegularCross (B : Real) (m : Nat)
    (F : Finset (Prod (Fin m) (Fin m))) : Matrix (Fin m) (Fin m) Real :=
  fun i j => (1 / (hamiltonianPrimeFactorRank B m : Real)) *
    (if Membership.mem F (i, j) then 1 else 0)

theorem hamiltonian_prime_regular_cross_reindex
    (B : Real) (m : Nat) (F : Finset (Prod (Fin m) (Fin m))) :
    (hamiltonianPrimeNormalizedFactor B m F).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) =
      bipartiteLift (hamiltonianPrimeRegularCross B m F) := by
  ext i j
  change (1 / (hamiltonianPrimeFactorRank B m : Real)) *
    hamiltonianFactorAdjacency F
      ((hamiltonianParityEquiv m).symm ((hamiltonianParityEquiv m) i))
      ((hamiltonianParityEquiv m).symm ((hamiltonianParityEquiv m) j)) =
    bipartiteLift (hamiltonianPrimeRegularCross B m F) i j
  simp only [Equiv.symm_apply_apply]
  cases i <;> cases j <;>
    simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose,
      hamiltonianFactorAdjacency, hamiltonianPrimeRegularCross]

theorem hamiltonian_prime_regular_cross_stochastic
    (B : Real) (m : Nat) (F : Finset (Prod (Fin m) (Fin m)))
    (h : HamiltonianPrimeFactorPacket B m F) :
    And (forall i, Finset.univ.sum (fun j => hamiltonianPrimeRegularCross B m F i j) = 1)
      (forall j, Finset.univ.sum (fun i => hamiltonianPrimeRegularCross B m F i j) = 1) := by
  have hrNat : 0 < hamiltonianPrimeFactorRank B m := by have hp := h.rank_positive; omega
  have hr : Not ((hamiltonianPrimeFactorRank B m : Real) = 0) :=
    ne_of_gt (Nat.cast_pos.mpr hrNat)
  constructor
  . intro i
    unfold hamiltonianPrimeRegularCross
    rw [<- Finset.mul_sum, hamiltonian_factor_left_row_count F i, h.left_regular i]
    field_simp [hr]
  . intro j
    unfold hamiltonianPrimeRegularCross
    rw [<- Finset.mul_sum, hamiltonian_factor_right_row_count F j, h.right_regular j]
    field_simp [hr]

theorem hamiltonian_prime_regular_cross_centered_norm
    (B : Real) (m : Nat) (hm : 1 <= m) (F : Finset (Prod (Fin m) (Fin m))) :
    norm (centeredKernel (hamiltonianPrimeRegularCross B m F) (1 / (m : Real))) =
      norm (hamiltonianPrimeNormalizedFactor B m F -
        hamiltonianRealConstantParityMatrix (2 * m)) := by
  have hd :
      (hamiltonianPrimeNormalizedFactor B m F -
        hamiltonianRealConstantParityMatrix (2 * m)).submatrix
          (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) =
      bipartiteLift (centeredKernel (hamiltonianPrimeRegularCross B m F) (1 / (m : Real))) := by
    change (hamiltonianPrimeNormalizedFactor B m F).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) -
      (hamiltonianRealConstantParityMatrix (2 * m)).submatrix
        (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) = _
    rw [hamiltonian_prime_regular_cross_reindex, hamiltonian_constant_parity_reindex m hm]
    ext i j
    cases i <;> cases j <;>
      simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose, centeredKernel,
        averagingKernel, Matrix.sub_apply]
  rw [<- hamiltonian_bipartite_lift_norm, <- hd, hamiltonian_reindex_matrix_norm]

theorem hamiltonian_prime_factor_eigenvalue_error
    (B : Real) (m : Nat) (hm : 1 <= m) (F : Finset (Prod (Fin m) (Fin m)))
    (h : HamiltonianPrimeFactorPacket B m F) (lambda rho : Real) (x : Fin (2 * m) -> Real)
    (hX : Exists (fun i => Not (x i = 0)))
    (hEigen : forall i, (hamiltonianPrimeNormalizedFactor B m F).mulVec x i = lambda * x i)
    (hOne : Not (lambda = 1)) (hMinus : Not (lambda = -(1 : Real)))
    (hNorm : norm (hamiltonianPrimeNormalizedFactor B m F -
      hamiltonianRealConstantParityMatrix (2 * m)) <= rho) :
    abs lambda <= rho := by
  let e := hamiltonianParityEquiv m
  let y := fun s => x (e s)
  have hY : Exists (fun s => Not (y s = 0)) := by
    choose i hi using hX
    refine Exists.intro (e.symm i) ?_
    simpa only [y, Equiv.apply_symm_apply] using hi
  have hPull : forall s,
      (bipartiteLift (hamiltonianPrimeRegularCross B m F)).mulVec y s = lambda * y s := by
    intro s
    calc
      _ = ((hamiltonianPrimeNormalizedFactor B m F).submatrix e e).mulVec y s := by
        rw [hamiltonian_prime_regular_cross_reindex]
      _ = Finset.univ.sum (fun t =>
          hamiltonianPrimeNormalizedFactor B m F (e s) (e t) * x (e t)) := rfl
      _ = Finset.univ.sum (fun j =>
          hamiltonianPrimeNormalizedFactor B m F (e s) j * x j) := hamiltonian_sum_reindex e
        (fun j => hamiltonianPrimeNormalizedFactor B m F (e s) j * x j)
      _ = lambda * y s := hEigen (e s)
  have hStoch := hamiltonian_prime_regular_cross_stochastic B m F h
  have hCross : norm (centeredKernel (hamiltonianPrimeRegularCross B m F) (1 / (m : Real))) <= rho := by
    rw [hamiltonian_prime_regular_cross_centered_norm B m hm F]
    exact hNorm
  exact hamiltonian_stochastic_bipartite_eigenvalue_bound
    (hamiltonianPrimeRegularCross B m F) (1 / (m : Real)) lambda rho y
    hStoch.1 hStoch.2 hY hPull hOne hMinus hCross

theorem hamiltonian_prime_raw_factor_eigenvalue_error
    (B : Real) (m : Nat) (hm : 1 <= m) (F : Finset (Prod (Fin m) (Fin m)))
    (h : HamiltonianPrimeFactorPacket B m F) (lambda rho : Real) (x : Fin (2 * m) -> Real)
    (hX : Exists (fun i => Not (x i = 0)))
    (hEigen : forall i, (hamiltonianPrimeFactorAdjacency m F).mulVec x i = lambda * x i)
    (hPlus : Not (lambda = (hamiltonianPrimeFactorRank B m : Real)))
    (hMinus : Not (lambda = -(hamiltonianPrimeFactorRank B m : Real)))
    (hNorm : norm (hamiltonianPrimeNormalizedFactor B m F -
      hamiltonianRealConstantParityMatrix (2 * m)) <= rho) :
    abs lambda <= rho * (hamiltonianPrimeFactorRank B m : Real) := by
  let r := (hamiltonianPrimeFactorRank B m : Real)
  have hrNat : 0 < hamiltonianPrimeFactorRank B m := by have hp := h.rank_positive; omega
  have hr : 0 < r := Nat.cast_pos.mpr hrNat
  have hratio : lambda = (lambda / r) * r :=
    (div_eq_iff (ne_of_gt hr)).mp (rfl : lambda / r = lambda / r)
  have hOne : Not (lambda / r = 1) := by
    intro he
    apply hPlus
    rw [he, one_mul] at hratio
    exact hratio
  have hNeg : Not (lambda / r = -(1 : Real)) := by
    intro he
    apply hMinus
    rw [he] at hratio
    simpa only [neg_mul, one_mul] using hratio
  have hNormalized : forall i,
      (hamiltonianPrimeNormalizedFactor B m F).mulVec x i = (lambda / r) * x i := by
    intro i
    change Finset.univ.sum (fun j =>
      ((1 / r) * hamiltonianPrimeFactorAdjacency m F i j) * x j) = (lambda / r) * x i
    calc
      _ = (1 / r) * (hamiltonianPrimeFactorAdjacency m F).mulVec x i := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (lambda / r) * x i := by rw [hEigen i]; ring
  have hv := hamiltonian_prime_factor_eigenvalue_error B m hm F h (lambda / r) rho x
    hX hNormalized hOne hNeg hNorm
  have hvMul := mul_le_mul_of_nonneg_right hv (le_of_lt hr)
  have hcancel : abs (lambda / r) * r = abs lambda := by
    rw [abs_div, abs_of_pos hr]
    field_simp [ne_of_gt hr]
  rw [hcancel] at hvMul
  exact hvMul

theorem hamiltonian_prime_factor_hermitian
    (m : Nat) (F : Finset (Prod (Fin m) (Fin m))) :
    (hamiltonianPrimeFactorAdjacency m F).IsHermitian := by
  change (hamiltonianPrimeFactorAdjacency m F).conjTranspose =
    hamiltonianPrimeFactorAdjacency m F
  ext i j
  change hamiltonianFactorAdjacency F ((hamiltonianParityEquiv m).symm j)
      ((hamiltonianParityEquiv m).symm i) =
    hamiltonianFactorAdjacency F ((hamiltonianParityEquiv m).symm i)
      ((hamiltonianParityEquiv m).symm j)
  exact hamiltonian_factor_adjacency_symmetric F _ _

theorem hamiltonian_prime_factor_native_eigenvalue_error
    (B : Real) (m : Nat) (hm : 1 <= m) (F : Finset (Prod (Fin m) (Fin m)))
    (h : HamiltonianPrimeFactorPacket B m F) (rho : Real) (i : Fin (2 * m))
    (hPlus : Not ((hamiltonian_prime_factor_hermitian m F).eigenvalues i =
      (hamiltonianPrimeFactorRank B m : Real)))
    (hMinus : Not ((hamiltonian_prime_factor_hermitian m F).eigenvalues i =
      -(hamiltonianPrimeFactorRank B m : Real)))
    (hNorm : norm (hamiltonianPrimeNormalizedFactor B m F -
      hamiltonianRealConstantParityMatrix (2 * m)) <= rho) :
    abs ((hamiltonian_prime_factor_hermitian m F).eigenvalues i) <=
      rho * (hamiltonianPrimeFactorRank B m : Real) := by
  apply hamiltonian_real_hermitian_eigenvalue_test
    (hamiltonianPrimeFactorAdjacency m F) (hamiltonian_prime_factor_hermitian m F)
    (hamiltonianPrimeFactorRank B m : Real) (-(hamiltonianPrimeFactorRank B m : Real))
    (rho * (hamiltonianPrimeFactorRank B m : Real)) ?_ i hPlus hMinus
  intro lambda x hX hEigen hp hm'
  exact hamiltonian_prime_raw_factor_eigenvalue_error B m hm F h lambda rho x
    hX hEigen hp hm' hNorm

end LPF
end PrimeFactorOscillations
