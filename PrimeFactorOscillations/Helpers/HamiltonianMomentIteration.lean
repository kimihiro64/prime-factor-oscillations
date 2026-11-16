/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianColumnMoments

/-! # Iterating the verified even-moment recurrence

This finite scalar iteration is the common quantitative consumer
for column moments and the actual stochastic cut-row signed sums.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem hamiltonian_moment_recurrence_iteration
    (M : Nat -> Real) (v B : Real) (hv : 0 <= v)
    (hZero : M 0 <= B)
    (hRec : forall k : Nat, M (k + 1) <= (2 * (k : Real) + 1) * v * M k)
    (k : Nat) :
    M k <= B * hamiltonianOddMomentFactor k * v ^ k := by
  induction k with
  | zero => simpa [hamiltonianOddMomentFactor] using hZero
  | succ k ih =>
      have hC : 0 <= (2 * (k : Real) + 1) * v :=
        mul_nonneg (by positivity) hv
      have h := (hRec k).trans (mul_le_mul_of_nonneg_left ih hC)
      rw [hamiltonian_odd_moment_factor_successor, pow_succ]
      convert h using 1 <;> ring

theorem hamiltonian_moment_recurrence_power_bound
    (M : Nat -> Real) (v B : Real) (hv : 0 <= v) (hB : 0 <= B)
    (hZero : M 0 <= B)
    (hRec : forall k : Nat, M (k + 1) <= (2 * (k : Real) + 1) * v * M k)
    (k : Nat) :
    M k <= B * (2 * v * (k : Real)) ^ k := by
  have hMain := hamiltonian_moment_recurrence_iteration M v B hv hZero hRec k
  calc
    _ <= B * (2 * (k : Real)) ^ k * v ^ k := by
      exact hMain.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hamiltonian_odd_moment_factor_bound k) hB)
        (pow_nonneg hv k))
    _ = _ := by
      rw [mul_assoc, <- mul_pow]
      congr 2
      ring

end PrimeFactorOscillations
