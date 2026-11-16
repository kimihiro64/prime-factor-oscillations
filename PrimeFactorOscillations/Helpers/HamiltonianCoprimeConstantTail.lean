/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeConstantBounds

/-! # An explicit uniform geometric tail for the actual arithmetic constant

The complete prime-product series is used on every odd modulus. Its
signed leading coefficient is retained, and every higher coefficient
is bounded only after the exact Euler cancellation.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_geometric_quarter_tail (M : Nat) :
    HasSum (fun j : Nat => (2 / 3 : Real) * (1 / 4 : Real) ^ (j + (M + 1)))
      ((2 / 9 : Real) * (1 / 4 : Real) ^ M) := by
  have hGeom : HasSum (fun j : Nat => (1 / 4 : Real) ^ j) (4 / 3 : Real) := by
    convert hasSum_geometric_of_norm_lt_one
      (by norm_num : norm (1 / 4 : Real) < 1) using 1 <;> norm_num
  have hScaled := hGeom.mul_left ((2 / 3 : Real) * (1 / 4 : Real) ^ (M + 1))
  convert hScaled using 1
  all_goals first | (funext j; rw [pow_add]; ring) | (rw [pow_succ]; ring)

theorem hamiltonian_coprime_constant_uniform_tail (n M : Nat) [NeZero n]
    (hOdd : Odd n) (hn : 1 < n) :
    0 <= Real.log (hamiltonianCoprimeArithmeticConstant n) -
      (Finset.range (M + 1)).sum (hamiltonianCoprimeLogCoefficient n) /\
    Real.log (hamiltonianCoprimeArithmeticConstant n) -
      (Finset.range (M + 1)).sum (hamiltonianCoprimeLogCoefficient n) <=
        (2 / 9 : Real) * (1 / 4 : Real) ^ M := by
  have hSeries : HasSum (hamiltonianCoprimeLogCoefficient n)
      (Real.log (hamiltonianCoprimeArithmeticConstant n)) :=
    hamiltonian_coprime_odd_constant_prime_product_series n hOdd hn
  have hTail : HasSum (fun j : Nat => hamiltonianCoprimeLogCoefficient n (j + (M + 1)))
      (Real.log (hamiltonianCoprimeArithmeticConstant n) -
        (Finset.range (M + 1)).sum (hamiltonianCoprimeLogCoefficient n)) := by
    apply (hasSum_nat_add_iff (M + 1)).mpr
    convert hSeries using 1 <;> ring
  have hZero : HasSum (fun _ : Nat => (0 : Real)) 0 := hasSum_zero
  have hLower := hasSum_le (fun j : Nat =>
    (hamiltonian_coprime_log_coefficient_bounds n (j + (M + 1)) hOdd (by omega)).1)
    hZero hTail
  have hUpper := hasSum_le (fun j : Nat =>
    (hamiltonian_coprime_log_coefficient_bounds n (j + (M + 1)) hOdd (by omega)).2)
    hTail (hamiltonian_geometric_quarter_tail M)
  exact And.intro hLower hUpper

theorem hamiltonian_coprime_constant_uniform_tail_abs (n M : Nat) [NeZero n]
    (hOdd : Odd n) (hn : 1 < n) :
    abs (Real.log (hamiltonianCoprimeArithmeticConstant n) -
      (Finset.range (M + 1)).sum (hamiltonianCoprimeLogCoefficient n)) <=
        (2 / 9 : Real) * (1 / 4 : Real) ^ M := by
  have h := hamiltonian_coprime_constant_uniform_tail n M hOdd hn
  rw [abs_of_nonneg h.1]
  exact h.2

theorem hamiltonian_coprime_constant_log_bounds (n : Nat) [NeZero n]
    (hOdd : Odd n) (hn : 1 < n) :
    1 <= Real.log (hamiltonianCoprimeArithmeticConstant n) /\
      Real.log (hamiltonianCoprimeArithmeticConstant n) <= (11 / 9 : Real) := by
  have h := hamiltonian_coprime_constant_uniform_tail n 0 hOdd hn
  norm_num [hamiltonianCoprimeLogCoefficient] at h
  constructor <;> linarith only [h.1, h.2]

theorem hamiltonian_coprime_constant_absolute_bounds (n : Nat) [NeZero n]
    (hOdd : Odd n) (hn : 1 < n) :
    Real.exp 1 <= hamiltonianCoprimeArithmeticConstant n /\
      hamiltonianCoprimeArithmeticConstant n <= Real.exp (11 / 9 : Real) := by
  have hLog := hamiltonian_coprime_constant_log_bounds n hOdd hn
  have hExp : Real.exp (Real.log (hamiltonianCoprimeArithmeticConstant n)) =
      hamiltonianCoprimeArithmeticConstant n :=
    Real.exp_log (hamiltonian_coprime_odd_constant_positive hOdd)
  have hLower := Real.exp_le_exp.mpr hLog.1
  have hUpper := Real.exp_le_exp.mpr hLog.2
  rw [hExp] at hLower hUpper
  exact And.intro hLower hUpper

end PrimeFactorOscillations
