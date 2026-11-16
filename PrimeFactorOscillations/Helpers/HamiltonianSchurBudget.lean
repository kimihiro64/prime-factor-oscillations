/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianL2Resolvent

/-! # Row and column mass control over either real or complex scalars

The weighted row square and dimension-free operator estimate are shared
with the previously proved complex prime-support correction. The real
instance controls the separate stochastic completion error; no signed
arithmetic main term is replaced by its unsigned coefficient mass.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {K : Type*} [RCLike K]
variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_weighted_row_square
    (v x : Iota -> K) :
    norm (Finset.univ.sum (fun j => v j * x j)) ^ 2 <=
      (Finset.univ.sum (fun j => norm (v j))) *
        Finset.univ.sum (fun j => norm (v j) * norm (x j) ^ 2) := by
  let S := Finset.univ.sum (fun j => norm (v j) * norm (x j))
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => Real.sqrt (norm (v j)))
    (fun j => Real.sqrt (norm (v j)) * norm (x j))
  have hCross : Finset.univ.sum (fun j =>
      Real.sqrt (norm (v j)) * (Real.sqrt (norm (v j)) * norm (x j))) = S := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [<- mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
  have hFirst : Finset.univ.sum (fun j => Real.sqrt (norm (v j)) ^ 2) =
      Finset.univ.sum (fun j => norm (v j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Real.sq_sqrt (norm_nonneg _)
  have hSecond : Finset.univ.sum (fun j => (Real.sqrt (norm (v j)) * norm (x j)) ^ 2) =
      Finset.univ.sum (fun j => norm (v j) * norm (x j) ^ 2) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  rw [hCross, hFirst, hSecond] at hCS
  have hNorm : norm (Finset.univ.sum (fun j => v j * x j)) <= S := by
    exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, S])
  have hS : 0 <= S := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hSquare := mul_le_mul hNorm hNorm (norm_nonneg _) hS
  nlinarith only [hSquare, hCS]

theorem hamiltonian_l2_row_column_budget (M : Matrix Iota Iota K)
    (r : Real) (hr : 0 <= r)
    (hRow : forall i, Finset.univ.sum (fun j => norm (M i j)) <= r)
    (hCol : forall j, Finset.univ.sum (fun i => norm (M i j)) <= r) :
    norm M <= r := by
  let op := (@Matrix.toEuclideanCLM K Iota _ _ _) M
  have hOp : norm op <= r := by
    apply ContinuousLinearMap.opNorm_le_bound op hr
    intro x
    let y := op x
    have hEach (i : Iota) : norm (y.ofLp i) ^ 2 <=
        r * Finset.univ.sum (fun j => norm (M i j) * norm (x.ofLp j) ^ 2) := by
      have h := hamiltonian_weighted_row_square (fun j => M i j) x.ofLp
      change norm (Finset.univ.sum (fun j => M i j * x.ofLp j)) ^ 2 <= _
      exact h.trans (mul_le_mul_of_nonneg_right (hRow i)
        (Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))))
    have hSquare : norm y ^ 2 <= (r * norm x) ^ 2 := by
      calc
        _ = Finset.univ.sum (fun i => norm (y.ofLp i) ^ 2) := EuclideanSpace.norm_sq_eq y
        _ <= Finset.univ.sum (fun i =>
            r * Finset.univ.sum (fun j => norm (M i j) * norm (x.ofLp j) ^ 2)) :=
          Finset.sum_le_sum (fun i _ => hEach i)
        _ = r * Finset.univ.sum (fun i =>
            Finset.univ.sum (fun j => norm (M i j) * norm (x.ofLp j) ^ 2)) :=
          (Finset.mul_sum _ _ _).symm
        _ = r * Finset.univ.sum (fun j =>
            Finset.univ.sum (fun i => norm (M i j) * norm (x.ofLp j) ^ 2)) := by
          rw [Finset.sum_comm]
        _ = r * Finset.univ.sum (fun j =>
            (Finset.univ.sum (fun i => norm (M i j))) * norm (x.ofLp j) ^ 2) := by
          simp_rw [Finset.sum_mul]
        _ <= r * Finset.univ.sum (fun j => r * norm (x.ofLp j) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hr
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_right (hCol j) (sq_nonneg _)
        _ = (r * norm x) ^ 2 := by
          rw [<- Finset.mul_sum, <- EuclideanSpace.norm_sq_eq]
          ring
    have hRight : 0 <= r * norm x := mul_nonneg hr (norm_nonneg _)
    nlinarith only [hSquare, hRight, norm_nonneg y]
  rwa [Matrix.l2_opNorm_toEuclideanCLM] at hOp

theorem hamiltonian_symmetric_row_budget (M : Matrix Iota Iota K)
    (hSym : forall i j, M i j = M j i) (r : Real) (hr : 0 <= r)
    (hRow : forall i, Finset.univ.sum (fun j => norm (M i j)) <= r) :
    norm M <= r := by
  apply hamiltonian_l2_row_column_budget M r hr hRow
  intro j
  have h := hRow j
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hSym i j]

end PrimeFactorOscillations
