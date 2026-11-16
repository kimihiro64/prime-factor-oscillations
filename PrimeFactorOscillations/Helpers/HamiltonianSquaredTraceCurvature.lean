/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRegularizedPower
import PrimeFactorOscillations.Helpers.HamiltonianTraceMomentMass

/-! # Height-free curvature of the regularized squared trace moment -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_squared_trace_curvature_bound
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (X : Matrix Iota Iota Real) (hX : X.IsHermitian)
    (p : Nat) (hp : 2 <= p) (hEven : Even p) (e : Real) (he : 0 < e) :
    let q : Real := 2 / (p : Real)
    let g : Real := Matrix.trace (A ^ p)
    hamiltonianTracePowerHessian A X p * q * (g + e) ^ (q - 1) +
      ((p : Real) * Matrix.trace (A ^ p.pred * X)) ^ 2 *
        q * (q - 1) * (g + e) ^ (q - 2) <=
      4 * (p.pred : Real) * (Fintype.card Iota : Real) ^ q * norm X ^ 2 := by
  let q : Real := 2 / (p : Real)
  let g : Real := Matrix.trace (A ^ p)
  let K : Real := 2 * (p : Real) * (p.pred : Real) * norm X ^ 2 *
    (Fintype.card Iota : Real) ^ q
  have hpPos : (0 : Real) < p := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hp)
  have hpNe : Not ((p : Real) = 0) := ne_of_gt hpPos
  have hpTwo : (2 : Real) <= p := by exact_mod_cast hp
  have hq0 : 0 <= q := div_nonneg (by norm_num) hpPos.le
  have hq1 : q <= 1 := (div_le_one hpPos).mpr hpTwo
  have hg : 0 <= g := hamiltonian_even_trace_power_nonnegative A hA p hEven
  have hK : 0 <= K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        (sq_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hExp : ((p : Real) - 2) / (p : Real) = 1 - q := by
    dsimp [q]
    field_simp
  have hBudget := hamiltonian_dimension_scaled_trace_hessian A hA X hX p hp hEven
  rw [hExp] at hBudget
  have h := hamiltonian_regularized_power_curvature g (g + e)
    (hamiltonianTracePowerHessian A X p)
    ((p : Real) * Matrix.trace (A ^ p.pred * X)) K q hg
    (by linarith) (by linarith) hK hq0 hq1 hBudget
  have hqp : q * (p : Real) = 2 := by dsimp [q]; field_simp
  have hConstant : q * K =
      4 * (p.pred : Real) * (Fintype.card Iota : Real) ^ q * norm X ^ 2 := by
    calc
      _ = 2 * (q * (p : Real)) * (p.pred : Real) * norm X ^ 2 *
          (Fintype.card Iota : Real) ^ q := by dsimp [K]; ring
      _ = _ := by rw [hqp]; ring
  rw [hConstant] at h
  exact h

end PrimeFactorOscillations
