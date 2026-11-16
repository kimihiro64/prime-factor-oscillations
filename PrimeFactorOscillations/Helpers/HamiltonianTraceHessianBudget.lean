/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianTracePowerDerivative
import PrimeFactorOscillations.Helpers.HamiltonianTraceSpectralBasis

/-! # The complete trace-power Hessian from actual row and column square budgets -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_matrix_row_square_budget (B : Matrix Iota Iota Real) (i : Iota) :
    Finset.univ.sum (fun k => B i k ^ 2) <= norm B ^ 2 := by
  have hId : Finset.univ.sum (fun k => B i k ^ 2) = (B * B.conjTranspose) i i := by
    change Finset.univ.sum (fun k => B i k ^ 2) =
      Finset.univ.sum (fun k => B i k * B i k)
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ = (B * B.conjTranspose) i i := hId
    _ <= abs ((B * B.conjTranspose) i i) := le_abs_self _
    _ <= norm (B * B.conjTranspose) := by
      simpa only [Real.norm_eq_abs] using l2_matrix_entry_le_norm (B * B.conjTranspose) i i
    _ <= norm B * norm B.conjTranspose := Matrix.l2_opNorm_mul _ _
    _ = _ := by rw [Matrix.l2_opNorm_conjTranspose]; ring

theorem hamiltonian_matrix_column_square_budget (B : Matrix Iota Iota Real) (k : Iota) :
    Finset.univ.sum (fun i => B i k ^ 2) <= norm B ^ 2 := by
  have h := hamiltonian_matrix_row_square_budget B.conjTranspose k
  change Finset.univ.sum (fun i => B i k ^ 2) <= norm B.conjTranspose ^ 2 at h
  rw [Matrix.l2_opNorm_conjTranspose] at h
  exact h

theorem hamiltonian_hermitian_mixed_trace_budget
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (X : Matrix Iota Iota Real) (hX : X.IsHermitian)
    (n j : Nat) (hj : j <= n) :
    Matrix.trace (A ^ j * X * A ^ (n - j) * X) <=
      2 * norm X ^ 2 * Finset.univ.sum (fun i => abs (hA.eigenvalues i) ^ n) := by
  let B := hamiltonianSpectralConjugate A hA X
  have hB : norm B <= norm X := hamiltonian_spectral_conjugate_norm A hA X
  have hSquare : norm B ^ 2 <= norm X ^ 2 := by
    nlinarith only [hB, norm_nonneg B, norm_nonneg X]
  rw [hamiltonian_hermitian_mixed_trace_pairs A hA X hX j (n - j)]
  exact hamiltonian_signed_mixed_return_power_bound B hA.eigenvalues (norm X ^ 2) n j hj
    (fun i => (hamiltonian_matrix_row_square_budget B i).trans hSquare)
    (fun k => (hamiltonian_matrix_column_square_budget B k).trans hSquare)

theorem hamiltonian_complete_trace_power_hessian_budget
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (X : Matrix Iota Iota Real) (hX : X.IsHermitian)
    (p : Nat) (hp : 2 <= p) :
    hamiltonianTracePowerHessian A X p <=
      2 * (p : Real) * (p.pred : Real) * norm X ^ 2 *
        Finset.univ.sum (fun i => abs (hA.eigenvalues i) ^ p.pred.pred) := by
  let n := p.pred.pred
  let c := 2 * norm X ^ 2 * Finset.univ.sum (fun i => abs (hA.eigenvalues i) ^ n)
  have hPred : p.pred = n + 1 := by
    dsimp [n]
    omega
  have hEach (j : Nat) (hj : Membership.mem (Finset.range p.pred) j) :
      Matrix.trace (A ^ (n - j) * X * A ^ j * X) <= c := by
    have hLt := Finset.mem_range.mp hj
    rw [hPred] at hLt
    have hNat : j <= n := Nat.le_of_lt_succ hLt
    have hSwap : Matrix.trace (A ^ (n - j) * X * A ^ j * X) =
        Matrix.trace (A ^ j * X * A ^ (n - j) * X) := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (A ^ (n - j) * X) (A ^ j * X)
    rw [hSwap]
    exact hamiltonian_hermitian_mixed_trace_budget A hA X hX n j hNat
  have hSum : (Finset.range p.pred).sum
      (fun j => Matrix.trace (A ^ (n - j) * X * A ^ j * X)) <= (p.pred : Real) * c := by
    calc
      _ <= (Finset.range p.pred).sum (fun _ => c) := Finset.sum_le_sum hEach
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold hamiltonianTracePowerHessian
  have hScaled := mul_le_mul_of_nonneg_left hSum (Nat.cast_nonneg p : (0 : Real) <= p)
  exact hScaled.trans_eq (by dsimp [c, n]; ring)

end PrimeFactorOscillations
