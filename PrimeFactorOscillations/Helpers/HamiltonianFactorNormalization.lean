/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorFloor

/-!
# Both normalization losses of a nearly full regular factor

The discarded adjacency and the changed degree normalization are retained
as distinct terms of the exact matrix identity before either is bounded.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_matrix_real_smul_norm
    (c : Real) (M : Matrix Iota Iota Real) :
    norm (SMul.smul c M) = norm c * norm M := by
  exact norm_smul c M

theorem hamiltonian_factor_normalization_identity
    (U J : Matrix Iota Iota Real) (D r : Real) (hr : Not (r = 0)) :
    SMul.smul (1 / r) J - U =
      SMul.smul (1 / r) (J - SMul.smul D U) +
        SMul.smul ((D - r) / r) U := by
  ext i j
  change (1 / r) * J i j - U i j =
    (1 / r) * (J i j - D * U i j) + ((D - r) / r) * U i j
  field_simp [hr]
  <;> ring

theorem hamiltonian_factor_normalization_bound
    (U J : Matrix Iota Iota Real) (D r eps : Real)
    (hD : 0 < D) (heps : 0 <= eps) (hepsOne : eps <= 1)
    (hrHalf : D / 2 <= r) (hrUpper : r <= D)
    (hDefect : D - r <= 10 * eps * D + 1)
    (hU : norm U <= 1 + eps)
    (hLoss : norm (SMul.smul D U - J) <= (1 + eps) * D - r) :
    norm (SMul.smul (1 / r) J - U) <= 62 * eps + 6 / D := by
  have hrPos : 0 < r := lt_of_lt_of_le (div_pos hD (by norm_num)) hrHalf
  have hr0 : Not (r = 0) := ne_of_gt hrPos
  have hInv : 0 <= 1 / r := div_nonneg (by norm_num) (le_of_lt hrPos)
  have hSlack : 0 <= (D - r) / r :=
    div_nonneg (sub_nonneg.mpr hrUpper) (le_of_lt hrPos)
  have hLoss' : norm (J - SMul.smul D U) <= (1 + eps) * D - r := by
    rw [norm_sub_rev]
    exact hLoss
  have hNorm :
      norm (SMul.smul (1 / r) J - U) <=
      (1 / r) * ((1 + eps) * D - r + (D - r) * (1 + eps)) := by
    rw [hamiltonian_factor_normalization_identity U J D r hr0]
    calc
      _ <= norm (SMul.smul (1 / r) (J - SMul.smul D U)) +
          norm (SMul.smul ((D - r) / r) U) := norm_add_le _ _
      _ = (1 / r) * norm (J - SMul.smul D U) + ((D - r) / r) * norm U := by
        rw [hamiltonian_matrix_real_smul_norm, hamiltonian_matrix_real_smul_norm,
          Real.norm_of_nonneg hInv,
          Real.norm_of_nonneg hSlack]
      _ <= (1 / r) * ((1 + eps) * D - r) + ((D - r) / r) * (1 + eps) :=
        add_le_add (mul_le_mul_of_nonneg_left hLoss' hInv)
          (mul_le_mul_of_nonneg_left hU hSlack)
      _ = _ := by ring
  have hLossUpper : (1 + eps) * D - r <= 11 * eps * D + 1 := by
    nlinarith only [hDefect]
  have hSlackTwo : (D - r) * (1 + eps) <= (D - r) * 2 :=
    mul_le_mul_of_nonneg_left (by linarith only [hepsOne]) (sub_nonneg.mpr hrUpper)
  have hTwoDefect := mul_le_mul_of_nonneg_right hDefect (by norm_num : (0 : Real) <= 2)
  have hNumerator :
      (1 + eps) * D - r + (D - r) * (1 + eps) <= 31 * eps * D + 3 := by
    nlinarith only [hLossUpper, hSlackTwo, hTwoDefect]
  have hInvBound : 1 / r <= 2 / D := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1)
      (div_pos hD (by norm_num)) hrHalf
    have heq : (1 : Real) / (D / 2) = 2 / D := by
      field_simp [ne_of_gt hD]
    exact h.trans_eq heq
  have hN0 : 0 <= 31 * eps * D + 3 := by positivity
  calc
    _ <= (1 / r) * ((1 + eps) * D - r + (D - r) * (1 + eps)) := hNorm
    _ <= (1 / r) * (31 * eps * D + 3) :=
      mul_le_mul_of_nonneg_left hNumerator hInv
    _ <= (2 / D) * (31 * eps * D + 3) :=
      mul_le_mul_of_nonneg_right hInvBound hN0
    _ = 62 * eps + 6 / D := by
      field_simp [ne_of_gt hD]
      <;> ring
