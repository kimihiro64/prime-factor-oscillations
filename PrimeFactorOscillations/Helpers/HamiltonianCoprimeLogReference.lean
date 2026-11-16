/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeConstantLimit
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeRelativeCount

/-! # Exact logarithmic corrections in the all-modulus arithmetic reference

The odd arithmetic constant and square-root factor remain explicit.
Their uniform bounds yield the complete logarithmic reference error.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCoprimeEntropyMain (n : Nat) : Real :=
  (n : Real) * (Real.log (n.totient : Real) - 1)

def hamiltonianCoprimeEntropyCorrection (n : Nat) : Real :=
  if Odd n then Real.log (hamiltonianCoprimeArithmeticConstant n) +
    (Real.log Real.pi - Real.log 2 - Real.log (n : Real)) / 2 else Real.log Real.pi

def hamiltonianCoprimeReferenceLogBudget : Real :=
  3 + abs (Real.log Real.pi) + abs (Real.log 2)

theorem hamiltonian_coprime_even_log_reference (n : Nat) (hn : 0 < n) :
    Real.log (hamiltonianCoprimeEvenReference n) =
      hamiltonianCoprimeEntropyMain n + Real.log Real.pi := by
  have hPhi : 0 < (n.totient : Real) := by exact_mod_cast Nat.totient_pos.mpr hn
  have hBase : 0 < (n.totient : Real) / Real.exp 1 := div_pos hPhi (Real.exp_pos 1)
  unfold hamiltonianCoprimeEvenReference hamiltonianCoprimeEntropyMain
  rw [Real.log_mul Real.pi_ne_zero (ne_of_gt (pow_pos hBase n)),
    Real.log_pow, Real.log_div (ne_of_gt hPhi) (Real.exp_ne_zero 1), Real.log_exp]
  ring

theorem hamiltonian_coprime_odd_log_reference (n : Nat) [NeZero n] (hOdd : Odd n) :
    Real.log (hamiltonianCoprimeOddStirlingReference n) =
      hamiltonianCoprimeEntropyMain n +
        (Real.log (hamiltonianCoprimeArithmeticConstant n) +
          (Real.log Real.pi - Real.log 2 - Real.log (n : Real)) / 2) := by
  have hnR : 0 < (n : Real) := by exact_mod_cast NeZero.pos n
  have hPhi : 0 < (n.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos n)
  have hBase : 0 < (n.totient : Real) / Real.exp 1 := div_pos hPhi (Real.exp_pos 1)
  have hC : 0 < hamiltonianCoprimeArithmeticConstant n :=
    hamiltonian_coprime_odd_constant_positive hOdd
  have hS : 0 < Real.sqrt (Real.pi / (2 * (n : Real))) :=
    Real.sqrt_pos.mpr (div_pos Real.pi_pos (by positivity))
  unfold hamiltonianCoprimeOddStirlingReference hamiltonianCoprimeEntropyMain
  rw [Real.log_mul (ne_of_gt (mul_pos hC hS)) (ne_of_gt (pow_pos hBase n)),
    Real.log_mul (ne_of_gt hC) (ne_of_gt hS),
    Real.log_sqrt (by positivity),
    Real.log_div Real.pi_ne_zero (ne_of_gt (by positivity : (0 : Real) < 2 * (n : Real))),
    Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hnR),
    Real.log_pow, Real.log_div (ne_of_gt hPhi) (Real.exp_ne_zero 1), Real.log_exp]
  ring

theorem hamiltonian_coprime_relative_log_reference (n : Nat) [NeZero n] :
    Real.log (hamiltonianCoprimeRelativeReference n) =
      hamiltonianCoprimeEntropyMain n + hamiltonianCoprimeEntropyCorrection n := by
  by_cases hOdd : Odd n
  case pos =>
    rw [hamiltonianCoprimeRelativeReference, if_pos hOdd,
      hamiltonianCoprimeEntropyCorrection, if_pos hOdd]
    exact hamiltonian_coprime_odd_log_reference n hOdd
  case neg =>
    rw [hamiltonianCoprimeRelativeReference, if_neg hOdd,
      hamiltonianCoprimeEntropyCorrection, if_neg hOdd]
    exact hamiltonian_coprime_even_log_reference n (NeZero.pos n)

theorem hamiltonian_log_twice_dimension_lower (n : Nat) (hn : 2 <= n) :
    1 <= Real.log (2 * (n : Real)) := by
  have hnR : (2 : Real) <= n := by exact_mod_cast hn
  have hPos : 0 < 2 * (n : Real) := by linarith only [hnR]
  exact ((Real.lt_log_iff_exp_lt hPos).mpr
    (Real.exp_one_lt_three.trans_le (by linarith only [hnR]))).le

theorem hamiltonian_coprime_log_correction_budget (n : Nat) [NeZero n] (hn : 3 <= n) :
    abs (hamiltonianCoprimeEntropyCorrection n) <=
      hamiltonianCoprimeReferenceLogBudget * Real.log (2 * (n : Real)) := by
  let A := abs (Real.log Real.pi)
  let B := abs (Real.log 2)
  let L := Real.log (2 * (n : Real))
  have hA : 0 <= A := abs_nonneg _
  have hB : 0 <= B := abs_nonneg _
  have hL : 1 <= L := hamiltonian_log_twice_dimension_lower n (by omega)
  have hLn : 0 <= Real.log (n : Real) := Real.log_nonneg (by exact_mod_cast (show 1 <= n by omega))
  have hLnL : Real.log (n : Real) <= L := by
    apply Real.log_le_log (by exact_mod_cast (NeZero.pos n))
    have hnR : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith only [hnR]
  have hConst := mul_le_mul_of_nonneg_left hL (by linarith only [hA, hB] : 0 <= 2 + A + B)
  have hBudgetNonneg : 0 <= hamiltonianCoprimeReferenceLogBudget := by
    unfold hamiltonianCoprimeReferenceLogBudget
    positivity
  by_cases hOdd : Odd n
  case pos =>
    have hC := hamiltonian_coprime_constant_log_bounds n hOdd (by omega)
    have hC0 : 0 <= Real.log (hamiltonianCoprimeArithmeticConstant n) := by linarith only [hC.1]
    have hSub : abs (Real.log Real.pi - Real.log 2 - Real.log (n : Real)) <=
        A + B + Real.log (n : Real) := by
      have hOne := abs_sub (Real.log Real.pi) (Real.log 2)
      have hTwo := abs_sub (Real.log Real.pi - Real.log 2) (Real.log (n : Real))
      rw [abs_of_nonneg hLn] at hTwo
      exact hTwo.trans (by dsimp only [A, B]; linarith only [hOne])
    have hSum := abs_add_le (Real.log (hamiltonianCoprimeArithmeticConstant n))
      ((Real.log Real.pi - Real.log 2 - Real.log (n : Real)) / 2)
    rw [abs_of_nonneg hC0, abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)] at hSum
    rw [hamiltonianCoprimeEntropyCorrection, if_pos hOdd]
    change abs (Real.log (hamiltonianCoprimeArithmeticConstant n) +
      (Real.log Real.pi - Real.log 2 - Real.log (n : Real)) / 2) <= (3 + A + B) * L
    have hDiv := div_le_div_of_nonneg_right hSub (by norm_num : (0 : Real) <= 2)
    nlinarith only [hSum, hDiv, hC.2, hConst, hLnL, hL, hA, hB]
  case neg =>
    rw [hamiltonianCoprimeEntropyCorrection, if_neg hOdd]
    have hToBudget : A <= hamiltonianCoprimeReferenceLogBudget := by
      change A <= 3 + A + B
      linarith only [hB]
    have hMul := mul_le_mul_of_nonneg_left hL hBudgetNonneg
    rw [mul_one] at hMul
    exact hToBudget.trans hMul

theorem hamiltonian_coprime_reference_log_error (n : Nat) [NeZero n] (hn : 3 <= n) :
    abs (Real.log (hamiltonianCoprimeRelativeReference n) -
      hamiltonianCoprimeEntropyMain n) <=
        hamiltonianCoprimeReferenceLogBudget * Real.log (2 * (n : Real)) := by
  rw [hamiltonian_coprime_relative_log_reference]
  simpa only [add_sub_cancel_left] using hamiltonian_coprime_log_correction_budget n hn

end PrimeFactorOscillations
