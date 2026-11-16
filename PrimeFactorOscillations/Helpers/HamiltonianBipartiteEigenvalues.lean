/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMatrixGeometry
import PrimeFactorOscillations.Helpers.HamiltonianSpectralCuts

/-!
# Literal nontrivial eigenvalues of a stochastic bipartite lift

The eigenvector equations force both block sums to vanish whenever the
eigenvalue differs from 1 and -1. The retained model therefore acts as zero.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_quadratic_mulVec
    (M : Matrix Iota Iota Real) (x : Iota -> Real) :
    hamiltonianQuadratic M x = Finset.univ.sum (fun i => x i * M.mulVec x i) := by
  simp only [hamiltonianQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem hamiltonian_eigenvalue_error_bound
    (M P : Matrix Iota Iota Real) (x : Iota -> Real) (lambda rho : Real)
    (hX : Exists (fun i => Not (x i = 0)))
    (hEigen : forall i, M.mulVec x i = lambda * x i)
    (hReference : forall i, P.mulVec x i = 0)
    (hNorm : norm (M - P) <= rho) :
    abs lambda <= rho := by
  let S := Finset.univ.sum (fun i => x i ^ 2)
  have hS : 0 < S := by
    choose i hi using hX
    have hsq : 0 < x i ^ 2 := sq_pos_of_ne_zero hi
    exact hsq.trans_le (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  have hQM : hamiltonianQuadratic M x = lambda * S := by
    rw [hamiltonian_quadratic_mulVec]
    simp_rw [hEigen]
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hQP : hamiltonianQuadratic P x = 0 := by
    rw [hamiltonian_quadratic_mulVec]
    simp_rw [hReference]
    simp only [mul_zero, Finset.sum_const_zero]
  have hQ := hamiltonian_quadratic_norm (M - P) x
  rw [hamiltonian_quadratic_sub, hQM, hQP, sub_zero, abs_mul, abs_of_pos hS] at hQ
  have hScale := mul_le_mul_of_nonneg_right hNorm (le_of_lt hS)
  have hFinal : abs lambda * S <= rho * S := hQ.trans hScale
  apply le_of_not_gt
  intro hBad
  exact (not_lt_of_ge hFinal) (mul_lt_mul_of_pos_right hBad hS)

theorem hamiltonian_bipartite_mulVec_left
    (C : Matrix Iota Iota Real) (x : Sum Iota Iota -> Real) (i : Iota) :
    (bipartiteLift C).mulVec x (Sum.inl i) =
      Finset.univ.sum (fun j => C i j * x (Sum.inr j)) := by
  simp [bipartiteLift, Matrix.fromBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem hamiltonian_bipartite_mulVec_right
    (C : Matrix Iota Iota Real) (x : Sum Iota Iota -> Real) (j : Iota) :
    (bipartiteLift C).mulVec x (Sum.inr j) =
      Finset.univ.sum (fun i => C i j * x (Sum.inl i)) := by
  simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]

theorem hamiltonian_bipartite_eigenvector_sums
    (C : Matrix Iota Iota Real) (x : Sum Iota Iota -> Real) (lambda : Real)
    (hRow : forall i, Finset.univ.sum (fun j => C i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => C i j) = 1)
    (hEigen : forall i, (bipartiteLift C).mulVec x i = lambda * x i)
    (hOne : Not (lambda = 1)) (hMinus : Not (lambda = -(1 : Real))) :
    And (Finset.univ.sum (fun i => x (Sum.inl i)) = 0)
      (Finset.univ.sum (fun i => x (Sum.inr i)) = 0) := by
  let su := Finset.univ.sum (fun i => x (Sum.inl i))
  let sv := Finset.univ.sum (fun i => x (Sum.inr i))
  have hL : lambda * su = sv := by
    dsimp only [su, sv]
    calc
      _ = Finset.univ.sum (fun i => lambda * x (Sum.inl i)) := by rw [Finset.mul_sum]
      _ = Finset.univ.sum (fun i => (bipartiteLift C).mulVec x (Sum.inl i)) :=
        Finset.sum_congr rfl (fun i _ => (hEigen (Sum.inl i)).symm)
      _ = Finset.univ.sum (fun i => Finset.univ.sum (fun j => C i j * x (Sum.inr j))) := by
        simp_rw [hamiltonian_bipartite_mulVec_left]
      _ = Finset.univ.sum (fun j => Finset.univ.sum (fun i => C i j * x (Sum.inr j))) :=
        Finset.sum_comm
      _ = Finset.univ.sum (fun j => x (Sum.inr j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [<- Finset.sum_mul, hCol j, one_mul]
  have hR : lambda * sv = su := by
    dsimp only [su, sv]
    calc
      _ = Finset.univ.sum (fun j => lambda * x (Sum.inr j)) := by rw [Finset.mul_sum]
      _ = Finset.univ.sum (fun j => (bipartiteLift C).mulVec x (Sum.inr j)) :=
        Finset.sum_congr rfl (fun j _ => (hEigen (Sum.inr j)).symm)
      _ = Finset.univ.sum (fun j => Finset.univ.sum (fun i => C i j * x (Sum.inl i))) := by
        simp_rw [hamiltonian_bipartite_mulVec_right]
      _ = Finset.univ.sum (fun i => Finset.univ.sum (fun j => C i j * x (Sum.inl i))) :=
        Finset.sum_comm
      _ = Finset.univ.sum (fun i => x (Sum.inl i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [<- Finset.sum_mul, hRow i, one_mul]
  have hplus : (lambda - 1) * (su + sv) = 0 := by nlinarith only [hL, hR]
  have hminus : (lambda + 1) * (su - sv) = 0 := by nlinarith only [hL, hR]
  have hOne' : Not (lambda - 1 = 0) := by intro h; apply hOne; linarith only [h]
  have hMinus' : Not (lambda + 1 = 0) := by intro h; apply hMinus; linarith only [h]
  have hp : su + sv = 0 := (mul_eq_zero.mp hplus).resolve_left hOne'
  have hm : su - sv = 0 := (mul_eq_zero.mp hminus).resolve_left hMinus'
  constructor
  . change su = 0
    linarith only [hp, hm]
  . change sv = 0
    linarith only [hp, hm]

theorem hamiltonian_stochastic_bipartite_eigenvalue_bound
    (C : Matrix Iota Iota Real) (q lambda rho : Real) (x : Sum Iota Iota -> Real)
    (hRow : forall i, Finset.univ.sum (fun j => C i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => C i j) = 1)
    (hX : Exists (fun i => Not (x i = 0)))
    (hEigen : forall i, (bipartiteLift C).mulVec x i = lambda * x i)
    (hOne : Not (lambda = 1)) (hMinus : Not (lambda = -(1 : Real)))
    (hNorm : norm (centeredKernel C q) <= rho) :
    abs lambda <= rho := by
  have hSums := hamiltonian_bipartite_eigenvector_sums C x lambda hRow hCol hEigen hOne hMinus
  let P : Matrix (Sum Iota Iota) (Sum Iota Iota) Real := bipartiteLift (averagingKernel q)
  have hReference : forall i, P.mulVec x i = 0 := by
    intro i
    cases i with
    | inl i =>
      rw [hamiltonian_bipartite_mulVec_left]
      change Finset.univ.sum (fun j => q * x (Sum.inr j)) = 0
      rw [<- Finset.mul_sum, hSums.2, mul_zero]
    | inr j =>
      rw [hamiltonian_bipartite_mulVec_right]
      change Finset.univ.sum (fun i => q * x (Sum.inl i)) = 0
      rw [<- Finset.mul_sum, hSums.1, mul_zero]
  have hDiff : bipartiteLift C - P = bipartiteLift (centeredKernel C q) := by
    ext i j
    cases i <;> cases j <;>
      simp [P, bipartiteLift, Matrix.fromBlocks, Matrix.transpose, centeredKernel,
        averagingKernel, Matrix.sub_apply]
  have hBound : norm (bipartiteLift C - P) <= rho := by
    rw [hDiff, hamiltonian_bipartite_lift_norm]
    exact hNorm
  exact hamiltonian_eigenvalue_error_bound (bipartiteLift C) P x lambda rho
    hX hEigen hReference hBound

end PrimeFactorOscillations
