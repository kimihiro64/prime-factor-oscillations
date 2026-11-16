/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianOneSidedTaylor
import PrimeFactorOscillations.Helpers.HamiltonianSquaredTraceCurvature

/-! # The actual one-step squared trace moment for a signed selected direction -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_hermitian_real_affine
    (A X : Matrix Iota Iota Real) (hA : A.IsHermitian) (hX : X.IsHermitian)
    (t : Real) :
    (A + HSMul.hSMul t X).IsHermitian := by
  change (A + HSMul.hSMul t X).conjTranspose = A + HSMul.hSMul t X
  apply Matrix.ext
  intro i j
  have hAij := congrArg (fun M : Matrix Iota Iota Real => M i j) hA
  have hXij := congrArg (fun M : Matrix Iota Iota Real => M i j) hX
  change A j i = A i j at hAij
  change X j i = X i j at hXij
  change A j i + t * X j i = A i j + t * X i j
  rw [hAij, hXij]

theorem hamiltonian_regularized_squared_trace_step
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (X : Matrix Iota Iota Real) (hX : X.IsHermitian)
    (p : Nat) (hp : 2 <= p) (hEven : Even p) (e : Real) (he : 0 < e)
    (hDirection : Matrix.trace (A ^ p.pred * X) <= 0) :
    (Matrix.trace ((A + X) ^ p) + e) ^ (2 / (p : Real)) <=
      (Matrix.trace (A ^ p) + e) ^ (2 / (p : Real)) +
        2 * (p.pred : Real) * (Fintype.card Iota : Real) ^
          (2 / (p : Real)) * norm X ^ 2 := by
  let q : Real := 2 / (p : Real)
  let g : Real -> Real := fun t => Matrix.trace ((A + HSMul.hSMul t X) ^ p)
  let g1 : Real -> Real := fun t =>
    (p : Real) * Matrix.trace ((A + HSMul.hSMul t X) ^ p.pred * X)
  let g2 : Real -> Real := fun t =>
    hamiltonianTracePowerHessian (A + HSMul.hSMul t X) X p
  let f : Real -> Real := fun t => (g t + e) ^ q
  let f1 : Real -> Real := fun t => g1 t * q * (g t + e) ^ (q - 1)
  let f2 : Real -> Real := fun t =>
    g2 t * q * (g t + e) ^ (q - 1) +
      (g1 t) ^ 2 * q * (q - 1) * (g t + e) ^ (q - 2)
  let B : Real := 4 * (p.pred : Real) * (Fintype.card Iota : Real) ^ q * norm X ^ 2
  have hT (t : Real) : (A + HSMul.hSMul t X).IsHermitian :=
    hamiltonian_hermitian_real_affine A X hA hX t
  have hg0 (t : Real) : 0 <= g t :=
    hamiltonian_even_trace_power_nonnegative _ (hT t) p hEven
  have hg (t : Real) : HasDerivAt g (g1 t) t :=
    hamiltonian_trace_power_hasDerivAt A X p t
  have hg1 (t : Real) : HasDerivAt g1 (g2 t) t :=
    hamiltonian_trace_power_second_hasDerivAt A X p t
  have hf (t : Real) : HasDerivAt f (f1 t) t :=
    hamiltonian_regularized_power_hasDerivAt g g1 t e q (hg t) (by linarith [hg0 t])
  have hf1 (t : Real) : HasDerivAt f1 (f2 t) t :=
    hamiltonian_regularized_power_second_hasDerivAt g g1 g2 t e q
      (hg t) (hg1 t) (by linarith [hg0 t])
  have hBound (t : Real) : f2 t <= B :=
    hamiltonian_squared_trace_curvature_bound _ (hT t) X hX p hp hEven e he
  have hpPos : (0 : Real) < p := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hp)
  have hq : 0 <= q := div_nonneg (by norm_num) hpPos.le
  have hFirst : g1 0 <= 0 := by
    simpa only [g1, zero_smul, add_zero] using
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg p : (0 : Real) <= p) hDirection
  have hFDir : f1 0 <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hFirst hq)
      (Real.rpow_nonneg (by linarith [hg0 0]) _)
  have h := hamiltonian_nonpositive_direction_taylor f f1 f2 B
    (fun t _ => hf t) (fun t _ => hf1 t) (fun t _ => hBound t) hFDir
  have hConst : B / 2 =
      2 * (p.pred : Real) * (Fintype.card Iota : Real) ^ q * norm X ^ 2 := by
    dsimp [B]
    ring
  rw [hConst] at h
  simpa only [f, g, q, zero_smul, one_smul, add_zero] using h

end PrimeFactorOscillations
