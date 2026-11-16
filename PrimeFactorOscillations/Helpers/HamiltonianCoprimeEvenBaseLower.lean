/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBalancedDeletedCycleLower
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeCrossBlock
import PrimeFactorOscillations.Helpers.HamiltonianCoprimePathBudget
import PrimeFactorOscillations.Helpers.HamiltonianPrincipalCycleTransport

/-! # Native balanced retained-cycle lower counts at every large even modulus -/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_coprime_retained_cross_cycle
    (k : Nat) [NeZero k] (i j : Fin k) :
    hamiltonianCycleSum
        (hamiltonianRetainedKernel (hamiltonianCoprimeCrossBlock k) {i} {j}) =
      hamiltonianPrincipalCycleSum (hamiltonianCoprimeKernel (n := 2 * k))
        {hamiltonianCoprimeParityEquiv k (Sum.inl i),
          hamiltonianCoprimeParityEquiv k (Sum.inr j)} := by
  let e := hamiltonianCoprimeParityEquiv k
  let D : Finset (Sum (Fin k) (Fin k)) := Finset.disjSum {i} {j}
  have hD : D = {Sum.inl i, Sum.inr j} := by
    ext x
    cases x <;> simp [D]
  have hMap : D.map e.toEmbedding = {e (Sum.inl i), e (Sum.inr j)} := by
    rw [hD]
    simp
  change hamiltonianPrincipalCycleSum (bipartiteLift (hamiltonianCoprimeCrossBlock k)) D = _
  rw [<- hamiltonian_coprime_cross_reindex]
  rw [hamiltonian_principal_cycle_reindex, hMap]

theorem hamiltonian_coprime_even_cross_cycle_lower_uniform :
    exists N0 : Nat, 512 <= N0 /\ forall k : Nat, N0 <= 2 * k ->
      forall [NeZero k], forall i j : Fin k,
        Real.exp (-((2 * k - 2 : Nat) : Real) -
            160 * (((2 * k : Nat) : Real) / ((2 * k).totient : Real))) /
          ((2 * k - 2 : Nat) : Real) <=
        hamiltonianPrincipalCycleSum (hamiltonianCoprimeKernel (n := 2 * k))
          {hamiltonianCoprimeParityEquiv k (Sum.inl i),
            hamiltonianCoprimeParityEquiv k (Sum.inr j)} := by
  let gamma := hamiltonianSublogCountDensity (3 / 4)
  have hGamma : 0 < gamma := by
    dsimp only [gamma, hamiltonianSublogCountDensity]
    positivity
  choose C hC hCount using
    stochastic_balanced_deleted_cycle_exponential_lower_uniform.{0}
      (1 / 2) (by norm_num) (by norm_num)
  choose B hB hBudget using hamiltonian_coprime_path_uniform_parameter_budget
    1 gamma (by norm_num) hGamma
  let N0 := max B (2 * C + 2)
  refine Exists.intro N0 (And.intro (hB.trans (le_max_left _ _)) ?_)
  intro k hk inst i j
  have hkB : B <= 2 * k := (le_max_left _ _).trans hk
  have hkC : 2 * C + 2 <= 2 * k := (le_max_right _ _).trans hk
  have hk512 : 512 <= 2 * k := hB.trans hkB
  have hkPos : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  let A := (((2 * k : Nat) : Real) / ((2 * k).totient : Real))
  have hPar := hBudget (2 * k) hkB
  have hPhiPos : 0 < ((2 * k).totient : Real) := by linarith only [hPar.1]
  have hRank : Fintype.card (Compl.compl ({j} : Finset (Fin k)) : Finset (Fin k)) =
      k - 1 := by simp
  have hq : (Fintype.card (Fin k) : Real) * (1 / (k : Real)) = 1 := by
    simp only [Fintype.card_fin]
    field_simp [ne_of_gt hkPos]
  have hCap (x y : Fin k) :
      hamiltonianCoprimeCrossBlock k x y <= A * (1 / (k : Real)) := by
    have hEq : A * (1 / (k : Real)) = 2 / ((2 * k).totient : Real) := by
      dsimp only [A]
      push_cast
      field_simp [ne_of_gt hkPos, ne_of_gt hPhiPos]
    rw [hEq]
    exact (hamiltonian_coprime_cross_entry_cap k x y).trans
      (div_le_div_of_nonneg_right (by norm_num) hPhiPos.le)
  have hSmall : (({j} : Finset (Fin k)).card : Real) *
      (A / (1 - (1 / 2 : Real))) ^ 3 * (1 / (k : Real)) <= 1 / 10000 := by
    simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    have hEq : (A / (1 - (1 / 2 : Real))) ^ 3 * (1 / (k : Real)) =
        16 * A ^ 3 / ((2 * k : Nat) : Real) := by
      push_cast
      field_simp [ne_of_gt hkPos]
      <;> ring
    rw [hEq]
    exact hPar.2.2.2.1
  have hDensity : 2 * A <=
      hamiltonianSublogCountDensity (1 - (1 - (1 / 2 : Real)) / 2) *
        Real.log (Fintype.card (Compl.compl ({j} : Finset (Fin k)) :
          Finset (Fin k)) : Real) := by
    rw [hRank]
    have hHalf : (2 * k - 2) / 2 = k - 1 := by omega
    have h := hPar.2.2.1
    rw [hHalf] at h
    norm_num only [show 1 - (1 - (1 / 2 : Real)) / 2 = 3 / 4 by norm_num]
    exact h
  have hBase := hCount (Fin k) (hamiltonianCoprimeCrossBlock k) {i} {j} (by simp)
    (1 / (k : Real)) A (by simp only [Fintype.card_fin]; omega) hq
    (hamiltonian_totient_ratio_ge_one (2 * k) (by omega))
    (hamiltonian_coprime_cross_row_sum k) (hamiltonian_coprime_cross_col_sum k)
    (hamiltonian_coprime_cross_nonnegative k) hCap
    (hamiltonian_coprime_cross_physical_gap k) hSmall (by rw [hRank]; omega) hDensity
  have hTwice : 2 * ((k - 1 : Nat) : Real) = ((2 * k - 2 : Nat) : Real) := by
    exact_mod_cast (show 2 * (k - 1) = 2 * k - 2 by omega)
  have hLower := hBase.2
  rw [hRank] at hLower
  simp only [Finset.card_singleton, Nat.cast_one] at hLower
  norm_num only [show (1 - (1 / 2 : Real)) = 1 / 2 by norm_num] at hLower
  have hExponent : -2 * ((k - 1 : Nat) : Real) - 80 * A / (1 / 2) =
      -((2 * k - 2 : Nat) : Real) - 160 * A := by rw [<- hTwice]; ring
  rw [hExponent, hTwice, hamiltonian_coprime_retained_cross_cycle] at hLower
  exact hLower

end PrimeFactorOscillations
