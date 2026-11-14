/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.HamiltonianGammaMoments

/-! # Exact signed central inverse-Gamma moments

The shift parametrization covers every admissible integer shape. These
are consequences of the actual integral moment theorem, with no independent
moment assumptions. They supply the cubic and quartic Taylor corrections.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem gammaInverseAverage_centered_second (m : Nat) :
    gammaInverseAverage (m + 2) (fun s => (s - 1) ^ 2) =
      1 / ((m : Real) + 1) := by
  have h := gammaInverseAverage_centered_binomial (m + 2) 2 (by omega)
  norm_num [Finset.sum_range_succ, Nat.choose] at h
  rw [h]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  have hFact : Not ((m.factorial : Real) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hPos1 : Not ((m : Real) + 1 = 0) := by
    linarith only [(show (0 : Real) <= (m : Real) from Nat.cast_nonneg m)]
  have hPos2 : Not ((m : Real) + 2 = 0) := by
    linarith only [(show (0 : Real) <= (m : Real) from Nat.cast_nonneg m)]
  field_simp [hFact, hPos1, hPos2]
  ring

theorem gammaInverseAverage_centered_third (m : Nat) :
    gammaInverseAverage (m + 3) (fun s => (s - 1) ^ 3) =
      4 / (((m : Real) + 2) * ((m : Real) + 1)) := by
  have h := gammaInverseAverage_centered_binomial (m + 3) 3 (by omega)
  norm_num [Finset.sum_range_succ, Nat.choose] at h
  rw [h]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  have hFact : Not ((m.factorial : Real) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hPos1 : Not ((m : Real) + 1 = 0) := by
    linarith only [(show (0 : Real) <= (m : Real) from Nat.cast_nonneg m)]
  have hPos2 : Not ((m : Real) + 2 = 0) := by
    linarith only [(show (0 : Real) <= (m : Real) from Nat.cast_nonneg m)]
  have hPos3 : Not ((m : Real) + 3 = 0) := by
    linarith only [(show (0 : Real) <= (m : Real) from Nat.cast_nonneg m)]
  field_simp [hFact, hPos1, hPos2, hPos3]
  ring

theorem gammaInverseAverage_centered_fourth (m : Nat) :
    gammaInverseAverage (m + 4) (fun s => (s - 1) ^ 4) =
      3 * ((m : Real) + 10) /
        (((m : Real) + 3) * ((m : Real) + 2) * ((m : Real) + 1)) := by
  have h := gammaInverseAverage_centered_binomial (m + 4) 4 (by omega)
  norm_num [Finset.sum_range_succ, Nat.choose] at h
  rw [h]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  have hFact : Not ((m.factorial : Real) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hPos1 : Not ((m : Real) + 1 = 0) := by
    linarith only [(show (0 : Real) <= (m : Real) from Nat.cast_nonneg m)]
  have hPos2 : Not ((m : Real) + 2 = 0) := by
    linarith only [(show (0 : Real) <= (m : Real) from Nat.cast_nonneg m)]
  have hPos3 : Not ((m : Real) + 3 = 0) := by
    linarith only [(show (0 : Real) <= (m : Real) from Nat.cast_nonneg m)]
  have hPos4 : Not ((m : Real) + 4 = 0) := by
    linarith only [(show (0 : Real) <= (m : Real) from Nat.cast_nonneg m)]
  field_simp [hFact, hPos1, hPos2, hPos3, hPos4]
  ring

end PrimeFactorOscillations
