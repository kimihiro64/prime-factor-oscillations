/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicCount
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeCountBudget
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeGap
import PrimeFactorOscillations.Helpers.HamiltonianMatrixGeometry

/-! # The actual Hamiltonian count for every sufficiently large odd modulus

The signed Ramanujan spectrum and the uniform totient bound are applied
to the native coprime-difference graph. The reference contains the actual
centered determinant and Gram factor; the complete error is retained.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_coprime_odd_count_uniform :
    exists N0 : Nat, 256 <= N0 /\
      forall (n : Nat) [NeZero n], N0 <= n -> Odd n ->
        0 < hamiltonianAperiodicCycleReference (hamiltonianCoprimeKernel (n := n))
          (1 / (n : Real)) /\
        abs (hamiltonianCycleSum (hamiltonianCoprimeKernel (n := n)) /
          hamiltonianAperiodicCycleReference (hamiltonianCoprimeKernel (n := n))
            (1 / (n : Real)) - 1) <= 17 * (n : Real) ^ (-(1 : Real) / 10) := by
  choose A hA hCount using
    stochastic_aperiodic_count_polylog_uniform (1 / 2) (by norm_num) (by norm_num)
  have hK : 0 < hamiltonianAperiodicErrorConstant (1 / 2) :=
    (hamiltonian_aperiodic_density_budget (1 / 2) (by norm_num)).1
  choose B hB hBudget using hamiltonian_coprime_count_density_budget
    (hamiltonianAperiodicErrorConstant (1 / 2)) hK
  refine Exists.intro (max A B) (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro n inst hn hOdd
  have hnA : A <= n := (le_max_left _ _).trans hn
  have hnB : B <= n := (le_max_right _ _).trans hn
  have hn256 : 256 <= n := hA.trans hnA
  have hnPos : 0 < n := by omega
  cases n with
  | zero => omega
  | succ k =>
    let T : Matrix (Fin (k + 1)) (Fin (k + 1)) Real :=
      hamiltonianCoprimeKernel (n := k + 1)
    let q : Real := 1 / ((k + 1 : Nat) : Real)
    let a : Real := ((k + 1 : Nat) : Real) / ((k + 1).totient : Real)
    have hnR : (0 : Real) < ((k + 1 : Nat) : Real) := by exact_mod_cast hnPos
    have hPhi : (0 : Real) < ((k + 1).totient : Real) := by
      exact_mod_cast Nat.totient_pos.mpr hnPos
    have hq : ((k + 1 : Nat) : Real) * q = 1 := by dsimp [q]; field_simp
    have hDensity := hBudget (k + 1) hnB
    have hUpper (i j : Fin (k + 1)) : T i j <= a * q := by
      have h := hamiltonian_coprime_kernel_entry_cap (n := k + 1) i j
      have hEq : a * q = 1 / ((k + 1).totient : Real) := by
        dsimp [a, q]
        field_simp
      rw [hEq]
      exact h
    have hNorm : norm (centeredKernel T q) <= 1 - (1 / 2 : Real) := by
      have hTransport := @hamiltonian_reindex_matrix_norm
        (ZMod (k + 1)) (Fin (k + 1))
        (inferInstance : Fintype (ZMod (k + 1))) (inferInstance : Fintype (Fin (k + 1)))
        (inferInstance : DecidableEq (ZMod (k + 1))) (inferInstance : DecidableEq (Fin (k + 1)))
        (Equiv.refl _) (centeredKernel (hamiltonianCoprimeKernel (n := k + 1))
          (1 / ((k + 1 : Nat) : Real)))
      have hNative := hamiltonian_coprime_odd_physical_gap hOdd
      have hTransfer : norm (centeredKernel T q) <= (1 / 2 : Real) :=
        hTransport.le.trans hNative
      linarith only [hTransfer]
    have hRaw := hCount (k + 1) hnA T q a hq hDensity.1 hDensity.2.1
      (hamiltonian_coprime_kernel_row_sum (n := k + 1))
      (hamiltonian_coprime_kernel_col_sum (n := k + 1))
      (hamiltonian_coprime_kernel_nonnegative (n := k + 1)) hUpper hNorm
    have hDet := hRaw.2.1
    have hGram := hRaw.2.2.1
    have hGramPos : 0 < realGramDeterminantFactor (centeredKernel T q) 1 :=
      lt_of_lt_of_le (by norm_num) hGram
    have hRef : 0 < hamiltonianAperiodicCycleReference T q := by
      unfold hamiltonianAperiodicCycleReference
      rw [Fintype.card_fin]
      exact mul_pos (mul_pos
        (div_pos (by exact_mod_cast Nat.factorial_pos (k + 1 - 1))
          (pow_pos hnR _)) hDet) hGramPos
    have hIdentity := hamiltonian_aperiodic_count_reference_identity T q
      (by simp only [Fintype.card_fin]; omega) (ne_of_gt hDet) (ne_of_gt hGramPos)
    have hError := hRaw.2.2.2
    rw [hIdentity] at hError
    exact And.intro hRef (hError.trans (hamiltonian_coprime_count_error_budget
      (k + 1) hnPos (hamiltonianAperiodicErrorConstant (1 / 2)) a hDensity.2.2))

end PrimeFactorOscillations
