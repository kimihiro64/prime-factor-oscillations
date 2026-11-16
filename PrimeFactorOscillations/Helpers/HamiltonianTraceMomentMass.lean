/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPowerMassInterpolation
import PrimeFactorOscillations.Helpers.HamiltonianTraceHessianBudget

/-! # Dimension-scaled trace-moment Hessian on even powers -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_even_trace_power_absolute
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (p : Nat) (hEven : Even p) :
    Matrix.trace (A ^ p) = Finset.univ.sum (fun i => abs (hA.eigenvalues i) ^ p) := by
  rw [hamiltonian_hermitian_trace_power A hA p]
  apply Finset.sum_congr rfl
  intro i _
  cases hEven with
  | intro k hk =>
    rw [hk, <- two_mul, pow_mul, pow_mul, sq_abs]

theorem hamiltonian_even_trace_power_nonnegative
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (p : Nat) (hEven : Even p) :
    0 <= Matrix.trace (A ^ p) := by
  rw [hamiltonian_even_trace_power_absolute A hA p hEven]
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg _) _)

theorem hamiltonian_dimension_scaled_trace_hessian
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (X : Matrix Iota Iota Real) (hX : X.IsHermitian)
    (p : Nat) (hp : 2 <= p) (hEven : Even p) :
    hamiltonianTracePowerHessian A X p <=
      2 * (p : Real) * (p.pred : Real) * norm X ^ 2 *
        (Fintype.card Iota : Real) ^ (2 / (p : Real)) *
          (Matrix.trace (A ^ p)) ^ (((p : Real) - 2) / (p : Real)) := by
  have h := hamiltonian_trace_power_mass_interpolation Finset.univ hA.eigenvalues p hp
  rw [Finset.card_univ, <- hamiltonian_even_trace_power_absolute A hA p hEven] at h
  have hPred : p.pred.pred = p - 2 := by
    simp only [Nat.pred_eq_sub_one]
    omega
  have hBudget := hamiltonian_complete_trace_power_hessian_budget A hA X hX p hp
  rw [hPred] at hBudget
  have hC : 0 <= 2 * (p : Real) * (p.pred : Real) * norm X ^ 2 := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (sq_nonneg _)
  exact hBudget.trans ((mul_le_mul_of_nonneg_left h hC).trans_eq (by ring))

end PrimeFactorOscillations
