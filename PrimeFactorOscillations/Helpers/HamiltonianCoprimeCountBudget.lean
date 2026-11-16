/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianTotientSublog

/-! # Uniform coprime density budgets in the full counting error

The squared density pays for the complete exponential loss. The same
all-modulus threshold supplies the entry cap required by the count theorem.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_coprime_count_density_budget (K : Real) (hK : 0 < K) :
    exists N0 : Nat, 3 <= N0 /\ forall n : Nat, N0 <= n ->
      1 <= (n : Real) / (n.totient : Real) /\
      (n : Real) / (n.totient : Real) <= Real.log (n : Real) /\
      K * ((n : Real) / (n.totient : Real)) ^ 2 <= Real.log (n : Real) / 90 := by
  let b := min 1 (1 / (90 * K))
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  choose N0 hN0 hBudget using hamiltonian_totient_squared_sublogarithmic b hb
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n hn
  have hn3 : 3 <= n := hN0.trans hn
  have hnPos : 0 < n := by omega
  have hOne := hamiltonian_totient_ratio_ge_one n hnPos
  have hA0 : 0 <= (n : Real) / (n.totient : Real) := le_trans (by norm_num) hOne
  have hSquare : (n : Real) / (n.totient : Real) <=
      ((n : Real) / (n.totient : Real)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hOne hA0
    nlinarith only [h]
  have hLog : 0 <= Real.log (n : Real) := Real.log_nonneg (by exact_mod_cast (by omega : 1 <= n))
  have hbOne : b <= 1 := min_le_left _ _
  have hbK : b <= 1 / (90 * K) := min_le_right _ _
  have hKNe : Not (K = 0) := ne_of_gt hK
  have hClear : K * (1 / (90 * K)) = 1 / 90 := by field_simp
  have hKb : K * b <= 1 / 90 := by
    calc
      _ <= K * (1 / (90 * K)) := mul_le_mul_of_nonneg_left hbK hK.le
      _ = _ := hClear
  have hCap : (n : Real) / (n.totient : Real) <= Real.log (n : Real) := by
    calc
      _ <= ((n : Real) / (n.totient : Real)) ^ 2 := hSquare
      _ <= b * Real.log (n : Real) := hBudget n hn
      _ <= 1 * Real.log (n : Real) := mul_le_mul_of_nonneg_right hbOne hLog
      _ = _ := one_mul _
  refine And.intro hOne (And.intro hCap ?_)
  calc
    _ <= K * (b * Real.log (n : Real)) := mul_le_mul_of_nonneg_left (hBudget n hn) hK.le
    _ = (K * b) * Real.log (n : Real) := by ring
    _ <= (1 / 90) * Real.log (n : Real) := mul_le_mul_of_nonneg_right hKb hLog
    _ = _ := by ring

theorem hamiltonian_coprime_count_error_budget (n : Nat) (hn : 0 < n)
    (K a : Real) (hBudget : K * a ^ 2 <= Real.log (n : Real) / 90) :
    17 * (n : Real) ^ (-(1 : Real) / 9) * Real.exp (K * a ^ 2) <=
      17 * (n : Real) ^ (-(1 : Real) / 10) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnR, Real.rpow_def_of_pos hnR, mul_assoc, <- Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : Real) <= 17)
  apply Real.exp_le_exp.mpr
  linarith only [hBudget]

end PrimeFactorOscillations
