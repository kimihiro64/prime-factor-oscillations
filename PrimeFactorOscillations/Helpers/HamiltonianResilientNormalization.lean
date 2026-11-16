/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorNormalization

/-! # Full normalization budget after locally bounded deletion

The discarded adjacency and the change of denominator are both retained.
This finite estimate places the actual resilient factor inside the
three-fifths relative-counting domain.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

theorem hamiltonian_resilient_factor_floor (D : Real) (hD : 1000 <= D) :
    let r := Nat.floor ((39 / 40 : Real) * D)
    And (1 <= r) (And ((97 / 100 : Real) * D <= (r : Real))
      (And ((r : Real) <= D) ((r : Real) <= (195 / 199 : Real) * D))) := by
  intro r
  have hD0 : 0 <= D := by linarith only [hD]
  have hu : (r : Real) <= (39 / 40 : Real) * D :=
    Nat.floor_le (mul_nonneg (by norm_num) hD0)
  have hl : (39 / 40 : Real) * D < (r : Real) + 1 := Nat.lt_floor_add_one _
  have hr : (1 : Real) <= (r : Real) := by linarith only [hD, hl]
  refine And.intro (by exact_mod_cast hr) (And.intro ?_ (And.intro ?_ ?_))
  . linarith only [hD, hl]
  . nlinarith only [hu, hD0]
  . nlinarith only [hu, hD0]

theorem hamiltonian_resilient_normalization
    {Iota : Type*} [Fintype Iota] [DecidableEq Iota]
    (U J : Matrix Iota Iota Real) (D r : Real)
    (hD : 0 < D) (hr : 0 < r)
    (hrLower : (97 / 100 : Real) * D <= r) (hrUpper : r <= D)
    (hU : norm U <= (1001 / 1000 : Real))
    (hLoss : norm (SMul.smul D U - J) <= (1001 / 1000 : Real) * D - r) :
    norm (SMul.smul (1 / r) J - U) <= (64 / 1000 : Real) := by
  have hi : 0 <= 1 / r := le_of_lt (div_pos (by norm_num) hr)
  have hc : 0 <= (D - r) / r := div_nonneg (sub_nonneg.mpr hrUpper) hr.le
  have hUnit : (1 / r) * r = 1 := by field_simp [ne_of_gt hr]
  have hScaled := mul_le_mul_of_nonneg_left hrLower hi
  have hBudget : (1 / r) * D <= (100 / 97 : Real) := by
    nlinarith only [hScaled, hUnit]
  have hReverse : norm (J - SMul.smul D U) <= (1001 / 1000 : Real) * D - r := by
    rw [norm_sub_rev]
    exact hLoss
  have hFirst := mul_le_mul_of_nonneg_left hReverse hi
  have hSecond := mul_le_mul_of_nonneg_left hU hc
  have hNorm : norm (SMul.smul (1 / r) J - U) <=
      (1 / r) * norm (J - SMul.smul D U) + ((D - r) / r) * norm U := by
    rw [hamiltonian_factor_normalization_identity U J D r (ne_of_gt hr)]
    have h := norm_add_le
      (SMul.smul (1 / r) (J - SMul.smul D U))
      (SMul.smul ((D - r) / r) U)
    rw [hamiltonian_matrix_real_smul_norm, hamiltonian_matrix_real_smul_norm,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hi, abs_of_nonneg hc] at h
    exact h
  have hCoef : (D - r) / r = (1 / r) * (D - r) := by ring
  rw [hCoef] at hSecond hNorm
  nlinarith only [hNorm, hFirst, hSecond, hBudget, hUnit]
