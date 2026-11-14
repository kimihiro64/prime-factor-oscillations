/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Helpers.HamiltonianNeumannBound
import PrimeFactorOscillations.Helpers.HamiltonianStochasticEnergy

/-! # Uniform entries of the actual stochastic resolvent

All matrix norms in this module are the scoped Euclidean operator norm.
The signed determinant cancellation is performed in the finite modules;
the present bounds control its resolvent coefficients. The final estimate
is derived from stochastic rows, the maximum entry and the centered norm.
It does not assume the desired entrywise resolvent bound.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [DecidableEq Iota] [Fintype Iota]

theorem l2_sandwich_entry_bound (A M C : Matrix Iota Iota Real) (i j : Iota) :
    norm ((A * M * C) i j) <=
      norm (WithLp.toLp 2 (fun k => A i k) : EuclideanSpace Real Iota) *
        norm M * norm (WithLp.toLp 2 (fun k => C k j) : EuclideanSpace Real Iota) := by
  let u : EuclideanSpace Real Iota := WithLp.toLp 2 (fun k => A i k)
  let v : EuclideanSpace Real Iota := WithLp.toLp 2 (fun k => C k j)
  let op := (@Matrix.toEuclideanCLM Real Iota _ _ _) M
  have hEntry : (A * M * C) i j = inner Real u (op v) := by
    rw [Matrix.inner_toEuclideanCLM M u v]
    rw [Matrix.mul_assoc]
    rfl
  rw [hEntry]
  change norm (inner Real u (op v)) <= norm u * norm M * norm v
  calc
    _ <= norm u * norm (op v) := norm_inner_le_norm _ _
    _ <= norm u * (norm op * norm v) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm op v) (norm_nonneg u)
    _ = norm u * norm M * norm v := by
      change norm u * (norm ((@Matrix.toEuclideanCLM Real Iota _ _ _) M) * norm v) = _
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      ring

variable [Nonempty Iota]

theorem l2_neumann_certificate (Q : Matrix Iota Iota Real) (rho : Real)
    (hNorm : norm Q <= rho) (hRho : rho < 1) :
    (1 - rho) * norm (Ring.inverse ((1 : Matrix Iota Iota Real) - Q)) <= 1 := by
  simpa using (neumann_norm_certificate Q rho hNorm hRho)

theorem gram_resolvent_certificate (B : Matrix Iota Iota Real) (rho : Real)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1) (hNorm : norm B <= rho) :
    (1 - rho ^ 2) *
      norm (Ring.inverse ((1 : Matrix Iota Iota Real) - B.transpose * B)) <= 1 := by
  have hTranspose : B.conjTranspose = B.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hGram : norm (B.transpose * B) = norm B * norm B := by
    simpa only [hTranspose] using Matrix.l2_opNorm_conjTranspose_mul_self B
  have hGramBound : norm (B.transpose * B) <= rho ^ 2 := by
    rw [hGram, pow_two]
    exact mul_le_mul hNorm hNorm (norm_nonneg B) hRho0
  have hSquare : rho ^ 2 < 1 := by
    have hProduct : 0 < (1 - rho) * (1 + rho) :=
      mul_pos (sub_pos.mpr hRho1) (by linarith)
    nlinarith only [hProduct]
  exact l2_neumann_certificate (B.transpose * B) (rho ^ 2) hGramBound hSquare

theorem stochastic_resolvent_entry_bound (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1) (hNorm : norm (centeredKernel T q) <= rho)
    (i j : Iota) :
    (1 - rho ^ 2) * norm
      ((centeredKernel T q *
        Ring.inverse ((1 : Matrix Iota Iota Real) -
          (centeredKernel T q).transpose * centeredKernel T q) *
            (centeredKernel T q).transpose) i j) <= (a - 1) * q := by
  let B := centeredKernel T q
  let M := Ring.inverse ((1 : Matrix Iota Iota Real) - B.transpose * B)
  let u : EuclideanSpace Real Iota := WithLp.toLp 2 (fun k => B i k)
  let v : EuclideanSpace Real Iota := WithLp.toLp 2 (fun k => B j k)
  have hu : norm u ^ 2 <= (a - 1) * q := by
    rw [EuclideanSpace.real_norm_sq_eq u]
    change Finset.sum Finset.univ (fun k => B i k ^ 2) <= (a - 1) * q
    exact stochastic_row_energy T q a hq hrow hnonneg hupper i
  have hv : norm v ^ 2 <= (a - 1) * q := by
    rw [EuclideanSpace.real_norm_sq_eq v]
    change Finset.sum Finset.univ (fun k => B j k ^ 2) <= (a - 1) * q
    exact stochastic_row_energy T q a hq hrow hnonneg hupper j
  have hProduct : norm u * norm v <= (a - 1) * q := by
    nlinarith only [hu, hv, sq_nonneg (norm u - norm v)]
  have hM : (1 - rho ^ 2) * norm M <= 1 :=
    gram_resolvent_certificate B rho hRho0 hRho1 hNorm
  have hSandwich : norm ((B * M * B.transpose) i j) <= norm u * norm M * norm v := by
    simpa only [Matrix.transpose_apply] using l2_sandwich_entry_bound B M B.transpose i j
  have hGap : 0 <= 1 - rho ^ 2 := by
    have hPositive : 0 < (1 - rho) * (1 + rho) :=
      mul_pos (sub_pos.mpr hRho1) (by linarith)
    nlinarith only [hPositive]
  change (1 - rho ^ 2) * norm ((B * M * B.transpose) i j) <= (a - 1) * q
  calc
    _ <= (1 - rho ^ 2) * (norm u * norm M * norm v) :=
      mul_le_mul_of_nonneg_left hSandwich hGap
    _ = (norm u * norm v) * ((1 - rho ^ 2) * norm M) := by ring
    _ <= (norm u * norm v) * 1 :=
      mul_le_mul_of_nonneg_left hM (mul_nonneg (norm_nonneg u) (norm_nonneg v))
    _ = norm u * norm v := mul_one _
    _ <= (a - 1) * q := hProduct

end PrimeFactorOscillations
