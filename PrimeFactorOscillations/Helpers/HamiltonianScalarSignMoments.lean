/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSignFlipMoments

/-! # Scalar signed moments from the complete matrix flip identity

One-by-one matrices retain the same full sign cube and every
coordinate compensation term. No independence from a selected
row coordinate or diagonal erasure is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {J : Type*} [Fintype J] [DecidableEq J]

def hamiltonianScalarSignSum (w : J -> Real) (e : J -> Bool) : Real :=
  Finset.univ.sum (fun j => hamiltonianSignValue (e j) * w j)

def hamiltonianScalarSignSummand (w : J -> Real) (j : J) : Matrix Unit Unit Real :=
  fun _ _ => w j

def hamiltonianScalarSignVariance (w : J -> Real) : Real :=
  Finset.univ.sum (fun j => w j ^ 2)

theorem hamiltonian_unit_matrix_trace (M : Matrix Unit Unit Real) :
    Matrix.trace M = M () () := by
  simp [Matrix.trace, Matrix.diag_apply]

theorem hamiltonian_unit_matrix_product_entry (M N : Matrix Unit Unit Real) :
    (M * N) () () = M () () * N () () := by
  simp [Matrix.mul_apply]

theorem hamiltonian_unit_matrix_power_entry (M : Matrix Unit Unit Real) (p : Nat) :
    (M ^ p) () () = M () () ^ p := by
  induction p with
  | zero => simp
  | succ p ih => rw [pow_succ, hamiltonian_unit_matrix_product_entry, ih, pow_succ]

theorem hamiltonian_scalar_sign_summand_hermitian (w : J -> Real) (j : J) :
    (hamiltonianScalarSignSummand w j).IsHermitian := by
  change (hamiltonianScalarSignSummand w j).conjTranspose = hamiltonianScalarSignSummand w j
  ext r s
  cases r
  cases s
  rfl

theorem hamiltonian_scalar_sign_matrix_entry (w : J -> Real) (e : J -> Bool) :
    hamiltonianSignMatrix (hamiltonianScalarSignSummand w) e () () =
      hamiltonianScalarSignSum w e := by
  simp only [hamiltonianSignMatrix, Matrix.sum_apply, hamiltonian_sign_smul_entry,
    hamiltonianScalarSignSummand, hamiltonianScalarSignSum]

theorem hamiltonian_scalar_sign_trace_power (w : J -> Real) (e : J -> Bool) (p : Nat) :
    Matrix.trace (hamiltonianSignMatrix (hamiltonianScalarSignSummand w) e ^ p) =
      hamiltonianScalarSignSum w e ^ p := by
  rw [hamiltonian_unit_matrix_trace, hamiltonian_unit_matrix_power_entry,
    hamiltonian_scalar_sign_matrix_entry]

theorem hamiltonian_scalar_sign_variance_entry (w : J -> Real) :
    hamiltonianSignVariance (hamiltonianScalarSignSummand w) () () =
      hamiltonianScalarSignVariance w := by
  simp only [hamiltonianSignVariance, Matrix.sum_apply, hamiltonian_unit_matrix_power_entry,
    hamiltonianScalarSignSummand, hamiltonianScalarSignVariance]

theorem hamiltonian_scalar_sign_variance_trace (w : J -> Real) (e : J -> Bool) (q : Nat) :
    Matrix.trace (hamiltonianSignVariance (hamiltonianScalarSignSummand w) *
      hamiltonianSignMatrix (hamiltonianScalarSignSummand w) e ^ q) =
      hamiltonianScalarSignVariance w * hamiltonianScalarSignSum w e ^ q := by
  rw [hamiltonian_unit_matrix_trace, hamiltonian_unit_matrix_product_entry,
    hamiltonian_scalar_sign_variance_entry, hamiltonian_unit_matrix_power_entry,
    hamiltonian_scalar_sign_matrix_entry]

theorem hamiltonian_scalar_sign_even_moment_recurrence
    (w : J -> Real) (q : Nat) (hEven : Even q) :
    Finset.univ.sum (fun e => hamiltonianScalarSignSum w e ^ (q + 2)) <=
      (((q + 1 : Nat) : Real) * hamiltonianScalarSignVariance w) *
        Finset.univ.sum (fun e => hamiltonianScalarSignSum w e ^ q) := by
  have h := hamiltonian_sign_trace_moment_variance_bound
    (hamiltonianScalarSignSummand w) (hamiltonian_scalar_sign_summand_hermitian w) q hEven
  simp_rw [hamiltonian_scalar_sign_trace_power, hamiltonian_scalar_sign_variance_trace] at h
  rw [<- Finset.mul_sum] at h
  simpa only [mul_assoc] using h

theorem hamiltonian_scalar_row_variance_bound
    (w : J -> Real) (alpha : Real)
    (hNonneg : forall j, 0 <= w j) (hCap : forall j, w j <= alpha)
    (hRow : Finset.univ.sum w = 1) :
    hamiltonianScalarSignVariance w <= alpha := by
  unfold hamiltonianScalarSignVariance
  calc
    _ <= Finset.univ.sum (fun j => alpha * w j) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hCap j) (hNonneg j)
    _ = alpha := by rw [<- Finset.mul_sum, hRow, mul_one]

theorem hamiltonian_scalar_sign_even_moment_nonnegative
    (w : J -> Real) (q : Nat) (hEven : Even q) :
    0 <= Finset.univ.sum (fun e => hamiltonianScalarSignSum w e ^ q) := by
  let r := hEven.choose
  have hQ : q = r + r := hEven.choose_spec
  rw [hQ]
  apply Finset.sum_nonneg
  intro e he
  rw [pow_add]
  exact mul_self_nonneg _

theorem hamiltonian_scalar_row_moment_recurrence
    (w : J -> Real) (alpha : Real)
    (hNonneg : forall j, 0 <= w j) (hCap : forall j, w j <= alpha)
    (hRow : Finset.univ.sum w = 1) (q : Nat) (hEven : Even q) :
    Finset.univ.sum (fun e => hamiltonianScalarSignSum w e ^ (q + 2)) <=
      (((q + 1 : Nat) : Real) * alpha) *
        Finset.univ.sum (fun e => hamiltonianScalarSignSum w e ^ q) := by
  have h := hamiltonian_scalar_sign_even_moment_recurrence w q hEven
  have hVariance := hamiltonian_scalar_row_variance_bound w alpha hNonneg hCap hRow
  have hProduct := mul_le_mul_of_nonneg_right hVariance
    (hamiltonian_scalar_sign_even_moment_nonnegative w q hEven)
  have hScaled := mul_le_mul_of_nonneg_left hProduct
    (show (0 : Real) <= ((q + 1 : Nat) : Real) from Nat.cast_nonneg _)
  exact h.trans (by simpa only [mul_assoc] using hScaled)

end PrimeFactorOscillations
