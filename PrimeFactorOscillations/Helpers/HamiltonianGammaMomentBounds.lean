/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.HamiltonianGammaMoments

/-! # Uniform raw inverse-Gamma moment bounds

The exact factorial formula gives the actual successive-moment identity.
It then yields the uniform bound needed for the truncated signed moments:
all moments through order eight are bounded when the shape parameter is at
least sixteen. No moment assumption or asymptotic constant is introduced.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem gammaInverseAverage_pow_step (n j : Nat) (hj : j + 1 <= n) :
    ((n - j : Nat) : Real) * gammaInverseAverage n (fun s => s ^ (j + 1)) =
      (n : Real) * gammaInverseAverage n (fun s => s ^ j) := by
  have hj0 : j <= n := by omega
  have hPred : n - j = (n - (j + 1)) + 1 := by omega
  rw [gammaInverseAverage_pow n (j + 1) hj, gammaInverseAverage_pow n j hj0,
    hPred, Nat.factorial_succ, pow_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem gammaInverseAverage_pow_le_two_pow (n j : Nat) (hRange : 2 * j <= n) :
    gammaInverseAverage n (fun s => s ^ j) <= (2 : Real) ^ j := by
  revert hRange
  induction j with
  | zero =>
      intro hRange
      rw [gammaInverseAverage_pow_zero]
      norm_num
  | succ j ih =>
      intro hRange
      have hj : j + 1 <= n := by omega
      have hj0 : j <= n := by omega
      have hInd := ih (by omega : 2 * j <= n)
      have hCoefficient : 0 < ((n - j : Nat) : Real) :=
        Nat.cast_pos.mpr (by omega)
      have hDouble : (n : Real) <= 2 * ((n - j : Nat) : Real) := by
        rw [Nat.cast_sub hj0]
        have hReal : 2 * (j : Real) <= (n : Real) := by
          exact_mod_cast (show 2 * j <= n by omega)
        linarith only [hReal]
      have hComparison :
          ((n - j : Nat) : Real) * gammaInverseAverage n (fun s => s ^ (j + 1)) <=
            ((n - j : Nat) : Real) * (2 : Real) ^ (j + 1) := by
        calc
          _ = (n : Real) * gammaInverseAverage n (fun s => s ^ j) :=
            gammaInverseAverage_pow_step n j hj
          _ <= (n : Real) * (2 : Real) ^ j :=
            mul_le_mul_of_nonneg_left hInd (Nat.cast_nonneg n)
          _ <= (2 * ((n - j : Nat) : Real)) * (2 : Real) ^ j :=
            mul_le_mul_of_nonneg_right hDouble (pow_nonneg (by norm_num) j)
          _ = ((n - j : Nat) : Real) * (2 : Real) ^ (j + 1) := by
            rw [pow_succ]
            ring
      by_contra hNot
      have hStrict :
          ((n - j : Nat) : Real) * (2 : Real) ^ (j + 1) <
            ((n - j : Nat) : Real) * gammaInverseAverage n (fun s => s ^ (j + 1)) :=
        mul_lt_mul_of_pos_left (lt_of_not_ge hNot) hCoefficient
      exact (not_lt_of_ge hComparison) hStrict

end PrimeFactorOscillations
