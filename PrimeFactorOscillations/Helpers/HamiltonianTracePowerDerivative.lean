/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import PrimeFactorOscillations.Helpers.HamiltonianTracePowerScalars

/-! # Scalar entry derivatives and the complete noncommutative trace Hessian

Only real-valued entries are differentiated. The exact finite power
direction and every mixed return remain in the two trace derivatives.
No matrix topology, commutation of the increment, or concentration
hypothesis is needed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianMatrixPowerDirection (A X : Matrix Iota Iota Real) (p : Nat) :
    Matrix Iota Iota Real :=
  (Finset.range p).sum (fun j => A ^ (p.pred - j) * X * A ^ j)

def hamiltonianTracePowerHessian (A X : Matrix Iota Iota Real) (p : Nat) : Real :=
  (p : Real) * (Finset.range p.pred).sum
    (fun j => Matrix.trace (A ^ (p.pred.pred - j) * X * A ^ j * X))

theorem hamiltonian_matrix_power_direction_succ
    (A X : Matrix Iota Iota Real) (n : Nat) :
    hamiltonianMatrixPowerDirection A X (n + 1) =
      A * hamiltonianMatrixPowerDirection A X n + X * A ^ n := by
  unfold hamiltonianMatrixPowerDirection
  rw [Nat.pred_succ, Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.sub_self, pow_zero, Matrix.one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hExp : n - j = (n.pred - j) + 1 := by
    have hlt := Finset.mem_range.mp hj
    rw [Nat.pred_eq_sub_one]
    omega
  rw [hExp, pow_succ']
  simp only [Matrix.mul_assoc]

theorem hamiltonian_trace_power_direction (A X : Matrix Iota Iota Real) (p : Nat) :
    Matrix.trace (hamiltonianMatrixPowerDirection A X p) =
      (p : Real) * Matrix.trace (A ^ p.pred * X) := by
  unfold hamiltonianMatrixPowerDirection
  rw [Matrix.trace_sum]
  calc
    _ = (Finset.range p).sum (fun _ => Matrix.trace (A ^ p.pred * X)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hLe : j <= p.pred := Nat.le_pred_of_lt (Finset.mem_range.mp hj)
      calc
        _ = Matrix.trace (A ^ j * A ^ (p.pred - j) * X) :=
          Matrix.trace_mul_cycle _ _ _
        _ = _ := by
          rw [<- pow_add, Nat.add_comm j (p.pred - j), Nat.sub_add_cancel hLe]
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem hamiltonian_matrix_affine_entry_hasDerivAt
    (A X : Matrix Iota Iota Real) (t : Real) (i j : Iota) :
    HasDerivAt (fun s : Real => (A + HSMul.hSMul s X) i j) (X i j) t := by
  change HasDerivAt (fun s : Real => A i j + s * X i j) (X i j) t
  simpa only [zero_add, one_mul] using!
    (hasDerivAt_const t (A i j)).add ((hasDerivAt_id t).mul_const (X i j))

theorem hamiltonian_matrix_power_entries_hasDerivAt
    (A X : Matrix Iota Iota Real) (p : Nat) (t : Real) :
    forall i j, HasDerivAt (fun s : Real => ((A + HSMul.hSMul s X) ^ p) i j)
      (hamiltonianMatrixPowerDirection (A + HSMul.hSMul t X) X p i j) t := by
  induction p with
  | zero =>
    intro i j
    simpa only [hamiltonianMatrixPowerDirection, Finset.range_zero,
      Finset.sum_empty, Matrix.zero_apply, pow_zero] using
        hasDerivAt_const t ((1 : Matrix Iota Iota Real) i j)
  | succ n ih =>
    intro i j
    have hMul := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hamiltonian_matrix_affine_entry_hasDerivAt A X t i k).mul (ih k j))
    rw [hamiltonian_matrix_power_direction_succ]
    simpa only [pow_succ', Matrix.mul_apply, Matrix.add_apply,
      Finset.sum_add_distrib, Pi.mul_apply, add_comm] using! hMul

theorem hamiltonian_matrix_power_times_entries_hasDerivAt
    (A X Y : Matrix Iota Iota Real) (p : Nat) (t : Real) (i j : Iota) :
    HasDerivAt (fun s : Real => ((A + HSMul.hSMul s X) ^ p * Y) i j)
      (((hamiltonianMatrixPowerDirection (A + HSMul.hSMul t X) X p) * Y) i j) t := by
  simpa only [Matrix.mul_apply] using!
    HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hamiltonian_matrix_power_entries_hasDerivAt A X p t i k).mul_const (Y k j))

theorem hamiltonian_trace_power_hasDerivAt
    (A X : Matrix Iota Iota Real) (p : Nat) (t : Real) :
    HasDerivAt (fun s : Real => Matrix.trace ((A + HSMul.hSMul s X) ^ p))
      ((p : Real) * Matrix.trace ((A + HSMul.hSMul t X) ^ p.pred * X)) t := by
  have hTrace := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    hamiltonian_matrix_power_entries_hasDerivAt A X p t i i)
  change HasDerivAt
    (fun s : Real => Matrix.trace ((A + HSMul.hSMul s X) ^ p))
    (Matrix.trace (hamiltonianMatrixPowerDirection (A + HSMul.hSMul t X) X p)) t at hTrace
  rw [hamiltonian_trace_power_direction] at hTrace
  exact hTrace

theorem hamiltonian_trace_power_second_hasDerivAt
    (A X : Matrix Iota Iota Real) (p : Nat) (t : Real) :
    HasDerivAt (fun s : Real =>
      (p : Real) * Matrix.trace ((A + HSMul.hSMul s X) ^ p.pred * X))
      (hamiltonianTracePowerHessian (A + HSMul.hSMul t X) X p) t := by
  let T := A + HSMul.hSMul t X
  have hTrace := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    hamiltonian_matrix_power_times_entries_hasDerivAt A X X p.pred t i i)
  change HasDerivAt
    (fun s : Real => Matrix.trace ((A + HSMul.hSMul s X) ^ p.pred * X))
    (Matrix.trace (hamiltonianMatrixPowerDirection T X p.pred * X)) t at hTrace
  have hId : Matrix.trace (hamiltonianMatrixPowerDirection T X p.pred * X) =
      (Finset.range p.pred).sum
        (fun j => Matrix.trace (T ^ (p.pred.pred - j) * X * T ^ j * X)) := by
    unfold hamiltonianMatrixPowerDirection
    rw [Finset.sum_mul, Matrix.trace_sum]
  rw [hId] at hTrace
  exact hTrace.const_mul (p : Real)

end PrimeFactorOscillations
