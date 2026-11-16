/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSquaredTraceStep
import PrimeFactorOscillations.Helpers.HamiltonianTraceNormReadout

/-! # The complete finite signed-direction trace-moment path bound -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_regularized_trace_path
    (Z X : Nat -> Matrix Iota Iota Real) (d p : Nat)
    (hp : 2 <= p) (hEven : Even p) (e : Real) (he : 0 < e)
    (hZ : forall i, i <= d -> (Z i).IsHermitian)
    (hX : forall i, i < d -> (X i).IsHermitian)
    (hStep : forall i, i < d -> Z (i + 1) = Z i + X i)
    (hDirection : forall i, i < d -> Matrix.trace ((Z i) ^ p.pred * X i) <= 0)
    (hNorm : forall i, i < d -> norm (X i) <= 2) :
    (Matrix.trace ((Z d) ^ p) + e) ^ (2 / (p : Real)) <=
      (Matrix.trace ((Z 0) ^ p) + e) ^ (2 / (p : Real)) +
        8 * (p.pred : Real) * (d : Real) *
          (Fintype.card Iota : Real) ^ (2 / (p : Real)) := by
  let F : Matrix Iota Iota Real -> Real :=
    fun A => (Matrix.trace (A ^ p) + e) ^ (2 / (p : Real))
  let c : Real := 8 * (p.pred : Real) *
    (Fintype.card Iota : Real) ^ (2 / (p : Real))
  have hOne (i : Nat) (hi : i < d) : F (Z (i + 1)) <= F (Z i) + c := by
    have h := hamiltonian_regularized_squared_trace_step
      (Z i) (hZ i (Nat.le_of_lt hi)) (X i) (hX i hi) p hp hEven e he (hDirection i hi)
    rw [<- hStep i hi] at h
    have hSquare : norm (X i) ^ 2 <= 4 := by
      nlinarith only [hNorm i hi, norm_nonneg (X i)]
    have hC : 0 <= 2 * (p.pred : Real) *
        (Fintype.card Iota : Real) ^ (2 / (p : Real)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hInc := mul_le_mul_of_nonneg_left hSquare hC
    have hCost : 2 * (p.pred : Real) *
        (Fintype.card Iota : Real) ^ (2 / (p : Real)) * norm (X i) ^ 2 <= c := by
      exact hInc.trans_eq (by dsimp [c]; ring)
    exact h.trans (add_le_add le_rfl hCost)
  have hInd : forall k, k <= d -> F (Z k) <= F (Z 0) + (k : Real) * c := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.cast_zero, zero_mul, add_zero, le_refl]
    | succ k ih =>
      intro hk
      have hkd : k < d := Nat.lt_of_succ_le hk
      calc
        _ <= F (Z k) + c := hOne k hkd
        _ <= (F (Z 0) + (k : Real) * c) + c :=
          add_le_add (ih (Nat.le_of_lt hkd)) le_rfl
        _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring
  exact (hInd d le_rfl).trans_eq (by dsimp [F, c]; ring)

theorem hamiltonian_regularized_trace_path_from_zero
    (Z X : Nat -> Matrix Iota Iota Real) (d p : Nat)
    (hp : 2 <= p) (hEven : Even p) (e : Real) (he : 0 < e)
    (hZero : Z 0 = 0)
    (hZ : forall i, i <= d -> (Z i).IsHermitian)
    (hX : forall i, i < d -> (X i).IsHermitian)
    (hStep : forall i, i < d -> Z (i + 1) = Z i + X i)
    (hDirection : forall i, i < d -> Matrix.trace ((Z i) ^ p.pred * X i) <= 0)
    (hNorm : forall i, i < d -> norm (X i) <= 2) :
    (Matrix.trace ((Z d) ^ p) + e) ^ (2 / (p : Real)) <=
      e ^ (2 / (p : Real)) + 8 * (p.pred : Real) * (d : Real) *
        (Fintype.card Iota : Real) ^ (2 / (p : Real)) := by
  have hp0 : Not (p = 0) := by omega
  have h := hamiltonian_regularized_trace_path Z X d p hp hEven e he
    hZ hX hStep hDirection hNorm
  simpa only [hZero, zero_pow hp0, Matrix.trace_zero, zero_add] using h

theorem hamiltonian_signed_trace_path_norm_bound
    (Z X : Nat -> Matrix Iota Iota Real) (d p : Nat)
    (hp : 2 <= p) (hEven : Even p) (e : Real) (he : 0 < e)
    (hZero : Z 0 = 0)
    (hZ : forall i, i <= d -> (Z i).IsHermitian)
    (hX : forall i, i < d -> (X i).IsHermitian)
    (hStep : forall i, i < d -> Z (i + 1) = Z i + X i)
    (hDirection : forall i, i < d -> Matrix.trace ((Z i) ^ p.pred * X i) <= 0)
    (hNorm : forall i, i < d -> norm (X i) <= 2) :
    norm (Z d) ^ 2 <= e ^ (2 / (p : Real)) +
      8 * (p.pred : Real) * (d : Real) *
        (Fintype.card Iota : Real) ^ (2 / (p : Real)) := by
  have hG : 0 <= Matrix.trace ((Z d) ^ p) :=
    hamiltonian_even_trace_power_nonnegative (Z d) (hZ d le_rfl) p hEven
  have hq : 0 <= 2 / (p : Real) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  calc
    _ <= (Matrix.trace ((Z d) ^ p)) ^ (2 / (p : Real)) :=
      hamiltonian_hermitian_norm_square_le_even_trace (Z d) (hZ d le_rfl) p hp hEven
    _ <= (Matrix.trace ((Z d) ^ p) + e) ^ (2 / (p : Real)) :=
      Real.rpow_le_rpow hG (by linarith only [he]) hq
    _ <= _ := hamiltonian_regularized_trace_path_from_zero Z X d p hp hEven e he
      hZero hZ hX hStep hDirection hNorm

theorem hamiltonian_signed_trace_path_unit_regularization
    (Z X : Nat -> Matrix Iota Iota Real) (d p : Nat)
    (hp : 2 <= p) (hEven : Even p)
    (hZero : Z 0 = 0)
    (hZ : forall i, i <= d -> (Z i).IsHermitian)
    (hX : forall i, i < d -> (X i).IsHermitian)
    (hStep : forall i, i < d -> Z (i + 1) = Z i + X i)
    (hDirection : forall i, i < d -> Matrix.trace ((Z i) ^ p.pred * X i) <= 0)
    (hNorm : forall i, i < d -> norm (X i) <= 2) :
    norm (Z d) ^ 2 <= 1 + 8 * (p.pred : Real) * (d : Real) *
      (Fintype.card Iota : Real) ^ (2 / (p : Real)) := by
  simpa only [Real.one_rpow] using
    hamiltonian_signed_trace_path_norm_bound Z X d p hp hEven 1 (by norm_num)
      hZero hZ hX hStep hDirection hNorm

end PrimeFactorOscillations
