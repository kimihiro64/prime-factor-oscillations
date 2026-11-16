/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeGap
import PrimeFactorOscillations.Helpers.HamiltonianCoprimePathBudget
import PrimeFactorOscillations.Helpers.HamiltonianPrincipalCycleTransport
import PrimeFactorOscillations.Helpers.HamiltonianPrincipalDeletedCycleLower

/-! # Native independent retained-cycle lower counts at every large odd modulus -/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_coprime_odd_interior_cycle_lower_uniform :
    exists N0 : Nat, 512 <= N0 /\ forall n : Nat, N0 <= n ->
      forall [NeZero n], Odd n -> forall a b : ZMod n, Not (a = b) ->
        Real.exp (-((n - 2 : Nat) : Real) -
            170 * ((n : Real) / (n.totient : Real)) + 5) /
          (4 * ((n - 2 : Nat) : Real)) <=
        hamiltonianPrincipalCycleSum (hamiltonianCoprimeKernel (n := n)) {a, b} := by
  let beta := hamiltonianAperiodicSublogDensity (1 / 4)
  have hBeta : 0 < beta := by
    dsimp only [beta, hamiltonianAperiodicSublogDensity,
      hamiltonianAperiodicErrorConstant]
    apply lt_min (by norm_num)
    positivity
  choose C hC hCount using
    stochastic_principal_deleted_cycle_exponential_lower_uniform.{0}
      (1 / 2) (by norm_num) (by norm_num)
  choose B hB hBudget using hamiltonian_coprime_path_uniform_parameter_budget
    beta 1 hBeta (by norm_num)
  let N0 := max B (C + 2)
  refine Exists.intro N0 (And.intro (hB.trans (le_max_left _ _)) ?_)
  intro n hn inst hOdd a b hab
  have hnB : B <= n := (le_max_left _ _).trans hn
  have hnC : C + 2 <= n := (le_max_right _ _).trans hn
  have hn512 : 512 <= n := hB.trans hnB
  let A := (n : Real) / (n.totient : Real)
  let D : Finset (ZMod n) := {a, b}
  have hPar := hBudget n hnB
  have hNPos : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hPhiPos : 0 < (n.totient : Real) := by linarith only [hPar.1]
  have hCard : Fintype.card (ZMod n) = n := ZMod.card n
  have hDCard : D.card = 2 := by simp only [D, Finset.card_pair hab]
  have hRank : Fintype.card (Compl.compl D : Finset (ZMod n)) = n - 2 :=
    (Fintype.card_congr (hamiltonianCoprimeInteriorComplementEquiv a b)).trans
      (hamiltonian_coprime_interior_card a b hab)
  have hq : (Fintype.card (ZMod n) : Real) * (1 / (n : Real)) = 1 := by
    rw [hCard]
    field_simp [ne_of_gt hNPos]
  have hCap (i j : ZMod n) :
      hamiltonianCoprimeKernel i j <= A * (1 / (n : Real)) := by
    have hEq : A * (1 / (n : Real)) = 1 / (n.totient : Real) := by
      dsimp only [A]
      field_simp [ne_of_gt hNPos, ne_of_gt hPhiPos]
    rw [hEq]
    exact hamiltonian_coprime_kernel_entry_cap i j
  have hSmall : (D.card : Real) * (A / (1 - (1 / 2 : Real))) ^ 3 *
      (1 / (n : Real)) <= 1 / 10000 := by
    rw [hDCard]
    simp only [Nat.cast_ofNat]
    have hEq : (2 : Real) * (A / (1 - (1 / 2 : Real))) ^ 3 *
        (1 / (n : Real)) = 16 * A ^ 3 / (n : Real) := by ring
    rw [hEq]
    exact hPar.2.2.2.1
  have hDensity : (2 * A) ^ 2 <=
      hamiltonianAperiodicSublogDensity ((1 - (1 / 2 : Real)) / 2) *
        Real.log (Fintype.card (Compl.compl D : Finset (ZMod n)) : Real) := by
    rw [hRank]
    norm_num only [show (1 - (1 / 2 : Real)) / 2 = 1 / 4 by norm_num]
    change (2 * A) ^ 2 <= beta * Real.log ((n - 2 : Nat) : Real)
    nlinarith only [hPar.2.1]
  have hBase := hCount (ZMod n) (hamiltonianCoprimeKernel (n := n)) D
    (1 / (n : Real)) A (by rw [hCard]; omega) hq
    (hamiltonian_totient_ratio_ge_one n (by omega))
    hamiltonian_coprime_kernel_row_sum hamiltonian_coprime_kernel_col_sum
    hamiltonian_coprime_kernel_nonnegative hCap
    (hamiltonian_coprime_odd_physical_gap hOdd) hSmall
    (by rw [hRank]; omega) hDensity
  have hExponent : -((n - 2 : Nat) : Real) -
      ((2 * A - 1) + (2 * A - 1) / ((1 - (1 / 2 : Real)) / 2)) -
        40 * (2 : Real) * A / (1 - (1 / 2 : Real)) =
      -((n - 2 : Nat) : Real) - 170 * A + 5 := by ring
  have hLower := hBase.2
  rw [hRank, hDCard] at hLower
  simp only [Nat.cast_ofNat] at hLower
  rw [hExponent] at hLower
  exact hLower

end PrimeFactorOscillations
