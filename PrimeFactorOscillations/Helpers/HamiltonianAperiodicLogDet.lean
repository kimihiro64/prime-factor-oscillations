/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorNormalization
import PrimeFactorOscillations.Helpers.HamiltonianFiniteFactorAmplification
import PrimeFactorOscillations.Helpers.HamiltonianMinorLogError
import PrimeFactorOscillations.Helpers.HamiltonianParityRootJets

/-! # The compensated nonsymmetric determinant direction

The signed linear trace is retained. Its remaining derivative is the
actual B-resolvent-B sandwich, controlled by both stochastic energy
budgets without an ambient-dimension loss. The maintained determinant
direction at zero is reused at each actual point of the path.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_affine_determinant_hasDerivAt_at
    (B : Matrix Iota Iota Real) (t : Real)
    (hUnit : IsUnit ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B)) :
    HasDerivAt (fun x : Real =>
      Matrix.det ((1 : Matrix Iota Iota Real) - HSMul.hSMul x B))
      (-Matrix.det ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B) *
        Matrix.trace (Ring.inverse
          ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B) * B)) t := by
  let M := (1 : Matrix Iota Iota Real) - HSMul.hSMul t B
  have hZero : HasDerivAt
      (fun x : Real => Matrix.det (M - HSMul.hSMul x B))
      (-Matrix.det M * Matrix.trace (Ring.inverse M * B)) (t - t) := by
    simpa only [sub_self] using hamiltonian_affine_determinant_hasDerivAt M B hUnit
  have hShift := HasDerivAt.comp (h := fun x : Real => x - t) t hZero
    ((hasDerivAt_id t).sub_const t)
  have hFunction : (fun x : Real => Matrix.det (M - HSMul.hSMul (x - t) B)) =
      (fun x : Real => Matrix.det
        ((1 : Matrix Iota Iota Real) - HSMul.hSMul x B)) := by
    funext x
    congr 1
    dsimp only [M]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    ring
  simp only [Function.comp_def] at hShift
  rw [hFunction] at hShift
  simpa only [mul_one] using! hShift

theorem hamiltonian_affine_log_determinant_hasDerivAt
    (B : Matrix Iota Iota Real) (t : Real)
    (hUnit : IsUnit ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B)) :
    HasDerivAt (fun x : Real =>
      Real.log (Matrix.det ((1 : Matrix Iota Iota Real) - HSMul.hSMul x B)))
      (-Matrix.trace (Ring.inverse
        ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B) * B)) t := by
  let M := (1 : Matrix Iota Iota Real) - HSMul.hSMul t B
  have hNe := hamiltonian_det_nonzero_of_right_inverse M (Ring.inverse M)
    (Ring.mul_inverse_cancel M hUnit)
  have h := (hamiltonian_affine_determinant_hasDerivAt_at B t hUnit).log hNe
  have hCancel :
      (-Matrix.det M * Matrix.trace (Ring.inverse M * B)) / Matrix.det M =
        -Matrix.trace (Ring.inverse M * B) := by field_simp
  change HasDerivAt _ ((-Matrix.det M * Matrix.trace (Ring.inverse M * B)) / Matrix.det M) t at h
  rw [hCancel] at h
  exact h

theorem stochastic_centered_sandwich_trace_bound
    (T M : Matrix Iota Iota Real) (q a delta : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (hDelta : 0 < delta)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j)
    (hUpper : forall i j, T i j <= a * q)
    (hM : delta * norm M <= 1) :
    delta * abs (Matrix.trace (centeredKernel T q * M * centeredKernel T q)) <= a - 1 := by
  let B := centeredKernel T q
  have hEntry (i : Iota) : delta * abs ((B * M * B) i i) <= (a - 1) * q := by
    let u : EuclideanSpace Real Iota := WithLp.toLp 2 (fun k => B i k)
    let v : EuclideanSpace Real Iota := WithLp.toLp 2 (fun k => B k i)
    have hu : norm u ^ 2 <= (a - 1) * q := by
      rw [EuclideanSpace.real_norm_sq_eq u]
      exact stochastic_row_energy T q a hq hRow hNonneg hUpper i
    have hv : norm v ^ 2 <= (a - 1) * q := by
      rw [EuclideanSpace.real_norm_sq_eq v]
      exact stochastic_column_energy T q a hq hCol hNonneg hUpper i
    have hProduct : norm u * norm v <= (a - 1) * q := by
      nlinarith only [hu, hv, sq_nonneg (norm u - norm v)]
    have hSandwich : abs ((B * M * B) i i) <= norm u * norm M * norm v := by
      simpa only [Real.norm_eq_abs] using l2_sandwich_entry_bound B M B i i
    calc
      _ <= delta * (norm u * norm M * norm v) :=
        mul_le_mul_of_nonneg_left hSandwich hDelta.le
      _ = (norm u * norm v) * (delta * norm M) := by ring
      _ <= (norm u * norm v) * 1 :=
        mul_le_mul_of_nonneg_left hM (mul_nonneg (norm_nonneg u) (norm_nonneg v))
      _ = norm u * norm v := mul_one _
      _ <= (a - 1) * q := hProduct
  calc
    _ <= delta * Finset.univ.sum (fun i => abs ((B * M * B) i i)) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hDelta.le
    _ = Finset.univ.sum (fun i => delta * abs ((B * M * B) i i)) := Finset.mul_sum _ _ _
    _ <= Finset.univ.sum (fun _ : Iota => (a - 1) * q) :=
      Finset.sum_le_sum (fun i _ => hEntry i)
    _ = a - 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc
        _ = (a - 1) * ((Fintype.card Iota : Real) * q) := by ring
        _ = _ := by rw [hq, mul_one]

end PrimeFactorOscillations
