/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteEigenvalues

/-! # One-sided eigenvalue comparison with the complete signed rank-two reference -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianSignedRankOneReference (u v : Iota -> Real) : Matrix Iota Iota Real :=
  fun i j => u i * u j - v i * v j

theorem hamiltonian_signed_rank_one_quadratic
    (u v x : Iota -> Real) :
    hamiltonianQuadratic (hamiltonianSignedRankOneReference u v) x =
      (Finset.univ.sum (fun i => u i * x i)) ^ 2 -
        (Finset.univ.sum (fun i => v i * x i)) ^ 2 := by
  calc
    _ = Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        (u i * x i) * (u j * x j) - (v i * x i) * (v j * x j))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [hamiltonianSignedRankOneReference]
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, <- Finset.mul_sum, <- Finset.sum_mul]
      ring

theorem hamiltonian_signed_rank_one_orthogonal_rayleigh
    (M : Matrix Iota Iota Real) (u v x : Iota -> Real) (rho : Real)
    (hNorm : norm (M - hamiltonianSignedRankOneReference u v) <= rho)
    (hOrth : Finset.univ.sum (fun i => u i * x i) = 0) :
    hamiltonianQuadratic M x <= rho * Finset.univ.sum (fun i => x i ^ 2) := by
  let P := hamiltonianSignedRankOneReference u v
  have hS : 0 <= Finset.univ.sum (fun i => x i ^ 2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hRef : hamiltonianQuadratic P x =
      -(Finset.univ.sum (fun i => v i * x i)) ^ 2 := by
    rw [hamiltonian_signed_rank_one_quadratic, hOrth]
    ring
  have hAbs := hamiltonian_quadratic_norm (M - P) x
  have hScale := mul_le_mul_of_nonneg_right hNorm hS
  have hUpper := (le_abs_self (hamiltonianQuadratic (M - P) x)).trans (hAbs.trans hScale)
  rw [hamiltonian_quadratic_sub, hRef] at hUpper
  nlinarith only [hUpper, sq_nonneg (Finset.univ.sum (fun i => v i * x i))]

theorem hamiltonian_two_orthogonal_vector_square_sum
    (x y : Iota -> Real) (a b : Real)
    (hXX : Finset.univ.sum (fun i => x i ^ 2) = 1)
    (hYY : Finset.univ.sum (fun i => y i ^ 2) = 1)
    (hXY : Finset.univ.sum (fun i => x i * y i) = 0) :
    Finset.univ.sum (fun i => (a * x i + b * y i) ^ 2) = a ^ 2 + b ^ 2 := by
  calc
    _ = Finset.univ.sum (fun i =>
        a ^ 2 * x i ^ 2 + (2 * a * b) * (x i * y i) + b ^ 2 * y i ^ 2) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    _ = _ := by
      simp only [Finset.sum_add_distrib, <- Finset.mul_sum, hXX, hYY, hXY,
        mul_one, mul_zero, add_zero]

theorem hamiltonian_two_orthogonal_eigenvector_quadratic
    (M : Matrix Iota Iota Real) (x y : Iota -> Real) (lambda mu a b : Real)
    (hXX : Finset.univ.sum (fun i => x i ^ 2) = 1)
    (hYY : Finset.univ.sum (fun i => y i ^ 2) = 1)
    (hXY : Finset.univ.sum (fun i => x i * y i) = 0)
    (hX : forall i, M.mulVec x i = lambda * x i)
    (hY : forall i, M.mulVec y i = mu * y i) :
    hamiltonianQuadratic M (fun i => a * x i + b * y i) =
      lambda * a ^ 2 + mu * b ^ 2 := by
  have hAction (i : Iota) :
      M.mulVec (fun j => a * x j + b * y j) i =
        a * lambda * x i + b * mu * y i := by
    calc
      _ = a * M.mulVec x i + b * M.mulVec y i := by
        change Finset.univ.sum (fun j => M i j * (a * x j + b * y j)) =
          a * Finset.univ.sum (fun j => M i j * x j) +
            b * Finset.univ.sum (fun j => M i j * y j)
        rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = _ := by rw [hX, hY]; ring
  rw [hamiltonian_quadratic_mulVec]
  simp_rw [hAction]
  calc
    _ = Finset.univ.sum (fun i =>
        (lambda * a ^ 2) * x i ^ 2 +
          (a * b * (lambda + mu)) * (x i * y i) +
            (mu * b ^ 2) * y i ^ 2) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    _ = _ := by
      simp only [Finset.sum_add_distrib, <- Finset.mul_sum, hXX, hYY, hXY,
        mul_one, mul_zero, add_zero]

theorem hamiltonian_two_scalar_kernel_witness (c d : Real) :
    exists a b : Real, a * c + b * d = 0 /\ 0 < a ^ 2 + b ^ 2 := by
  by_cases hc : c = 0
  . refine Exists.intro 1 (Exists.intro 0 ?_)
    rw [hc]
    norm_num
  . refine Exists.intro d (Exists.intro (-c) ?_)
    constructor
    . ring
    . have h := sq_pos_of_ne_zero hc
      nlinarith only [h, sq_nonneg d]

theorem hamiltonian_signed_rank_one_no_two_upper_eigenvectors
    (M : Matrix Iota Iota Real) (u v x y : Iota -> Real) (rho lambda mu : Real)
    (hNorm : norm (M - hamiltonianSignedRankOneReference u v) <= rho)
    (hXX : Finset.univ.sum (fun i => x i ^ 2) = 1)
    (hYY : Finset.univ.sum (fun i => y i ^ 2) = 1)
    (hXY : Finset.univ.sum (fun i => x i * y i) = 0)
    (hX : forall i, M.mulVec x i = lambda * x i)
    (hY : forall i, M.mulVec y i = mu * y i)
    (hLambda : rho < lambda) (hMu : rho < mu) : False := by
  let c := Finset.univ.sum (fun i => u i * x i)
  let d := Finset.univ.sum (fun i => u i * y i)
  choose a b hCoeff hNonzero using hamiltonian_two_scalar_kernel_witness c d
  have hOrth : Finset.univ.sum (fun i => u i * (a * x i + b * y i)) = 0 := by
    calc
      _ = a * c + b * d := by
        dsimp [c, d]
        rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := hCoeff
  have hUpper := hamiltonian_signed_rank_one_orthogonal_rayleigh M u v
    (fun i => a * x i + b * y i) rho hNorm hOrth
  rw [hamiltonian_two_orthogonal_vector_square_sum x y a b hXX hYY hXY,
    hamiltonian_two_orthogonal_eigenvector_quadratic M x y lambda mu a b
      hXX hYY hXY hX hY] at hUpper
  have hFirst : 0 <= (lambda - rho) * a ^ 2 :=
    mul_nonneg (sub_pos.mpr hLambda).le (sq_nonneg a)
  have hSecond : 0 <= (mu - rho) * b ^ 2 :=
    mul_nonneg (sub_pos.mpr hMu).le (sq_nonneg b)
  have hPositive : 0 < (lambda - rho) * a ^ 2 + (mu - rho) * b ^ 2 := by
    by_cases ha : a = 0
    . have hb : 0 < b ^ 2 := by simpa [ha] using hNonzero
      have h := mul_pos (sub_pos.mpr hMu) hb
      linarith only [h, hFirst]
    . have h := mul_pos (sub_pos.mpr hLambda) (sq_pos_of_ne_zero ha)
      linarith only [h, hSecond]
  nlinarith only [hUpper, hPositive]

end PrimeFactorOscillations
