/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimePhysicalScaling

/-! # Exact signed Dirichlet identities and the operator-error cut consumer -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianQuadratic (M : Matrix Iota Iota Real) (x : Iota -> Real) : Real :=
  Finset.univ.sum (fun i => Finset.univ.sum (fun j => x i * M i j * x j))

def hamiltonianDirichlet (M : Matrix Iota Iota Real) (x : Iota -> Real) : Real :=
  (1 / 2 : Real) * Finset.univ.sum
    (fun i => Finset.univ.sum (fun j => M i j * (x i - x j) ^ 2))

theorem hamiltonian_quadratic_norm (M : Matrix Iota Iota Real) (x : Iota -> Real) :
    abs (hamiltonianQuadratic M x) <=
      norm M * Finset.univ.sum (fun i => x i ^ 2) := by
  let v : EuclideanSpace Real Iota := WithLp.toLp 2 x
  let op := (@Matrix.toEuclideanCLM Real Iota _ _ _) M
  have hId : hamiltonianQuadratic M x = inner Real v (op v) := by
    rw [Matrix.inner_toEuclideanCLM]
    change Finset.univ.sum (fun i => Finset.univ.sum (fun j => x i * M i j * x j)) =
      dotProduct x (M.mulVec x)
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hId, <- Real.norm_eq_abs]
  calc
    _ <= norm v * norm (op v) := norm_inner_le_norm _ _
    _ <= norm v * (norm op * norm v) :=
      mul_le_mul_of_nonneg_left (op.le_opNorm v) (norm_nonneg v)
    _ = norm M * norm v ^ 2 := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      ring
    _ = _ := by rw [EuclideanSpace.real_norm_sq_eq]

theorem hamiltonian_quadratic_sub (M P : Matrix Iota Iota Real) (x : Iota -> Real) :
    hamiltonianQuadratic (M - P) x = hamiltonianQuadratic M x - hamiltonianQuadratic P x := by
  unfold hamiltonianQuadratic
  simp only [Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem hamiltonian_dirichlet_identity (M : Matrix Iota Iota Real)
    (hSymm : forall i j, M i j = M j i) (x : Iota -> Real) :
    hamiltonianDirichlet M x =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => M i j) * x i ^ 2) -
        hamiltonianQuadratic M x := by
  let R := Finset.univ.sum (fun i => Finset.univ.sum (fun j => M i j * x i ^ 2))
  let C := Finset.univ.sum (fun i => Finset.univ.sum (fun j => M i j * x j ^ 2))
  have hRow : R = Finset.univ.sum
      (fun i => Finset.univ.sum (fun j => M i j) * x i ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [<- Finset.sum_mul]
  have hCol : C = R := by
    dsimp only [C, R]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hSymm j i]
  have hFactor : Finset.univ.sum (fun i => Finset.univ.sum
      (fun j => 2 * (x i * M i j * x j))) = 2 * hamiltonianQuadratic M x := by
    simp only [hamiltonianQuadratic, Finset.mul_sum]
  have hExpand : Finset.univ.sum (fun i => Finset.univ.sum
      (fun j => M i j * (x i - x j) ^ 2)) = R + C - 2 * hamiltonianQuadratic M x := by
    calc
      _ = Finset.univ.sum (fun i => Finset.univ.sum
          (fun j => M i j * x i ^ 2 + M i j * x j ^ 2 - 2 * (x i * M i j * x j))) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hFactor]
        rfl
  unfold hamiltonianDirichlet
  rw [hExpand, hCol, hRow]
  ring

theorem hamiltonian_dirichlet_shift (M : Matrix Iota Iota Real)
    (x : Iota -> Real) (c : Real) :
    hamiltonianDirichlet M (fun i => x i + c) = hamiltonianDirichlet M x := by
  unfold hamiltonianDirichlet
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show x i + c - (x j + c) = x i - x j by ring]

theorem hamiltonian_dirichlet_reference_bound (M P : Matrix Iota Iota Real)
    (x : Iota -> Real) (d rho : Real)
    (hSymm : forall i j, M i j = M j i)
    (hDegree : forall i, d <= Finset.univ.sum (fun j => M i j))
    (hReference : hamiltonianQuadratic P x <= 0) (hNorm : norm (M - P) <= rho) :
    (d - rho) * Finset.univ.sum (fun i => x i ^ 2) <= hamiltonianDirichlet M x := by
  have hSquares : 0 <= Finset.univ.sum (fun i => x i ^ 2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hError := (le_abs_self (hamiltonianQuadratic (M - P) x)).trans
    (hamiltonian_quadratic_norm (M - P) x)
  have hUpper := mul_le_mul_of_nonneg_right hNorm hSquares
  rw [hamiltonian_quadratic_sub] at hError
  have hDiagonal : d * Finset.univ.sum (fun i => x i ^ 2) <=
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => M i j) * x i ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hDegree i) (sq_nonneg _))
  rw [hamiltonian_dirichlet_identity M hSymm]
  nlinarith only [hError, hUpper, hReference, hDiagonal]

end PrimeFactorOscillations
