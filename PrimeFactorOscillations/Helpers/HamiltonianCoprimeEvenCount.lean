/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteStirlingLimit
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeCrossBlock
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeUnorientedCount
import PrimeFactorOscillations.Helpers.HamiltonianTotientSublog

/-! # The complete actual even coprime-circle count

The full signed bipartite count is applied to the actual stochastic
cross block. The original arithmetic density, native cycle transport,
common edge weights and reversal factor are all consumed explicitly.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCoprimeEvenReference (n : Nat) : Real :=
  Real.pi * ((n.totient : Real) / Real.exp 1) ^ n

theorem hamiltonian_coprime_even_reference_identity (n : Nat) :
    hamiltonianCoprimeEvenReference n =
      (n.totient : Real) ^ n * (Real.pi * Real.exp (-(n : Real))) := by
  have hExp : Real.exp (n : Real) = (Real.exp 1) ^ n := by
    simpa only [mul_one] using Real.exp_nat_mul 1 n
  unfold hamiltonianCoprimeEvenReference
  rw [Real.exp_neg, hExp, div_pow]
  ring

theorem hamiltonian_coprime_even_reference_positive (n : Nat) (hn : 0 < n) :
    0 < hamiltonianCoprimeEvenReference n := by
  have hPhi : 0 < (n.totient : Real) := by exact_mod_cast Nat.totient_pos.mpr hn
  exact mul_pos Real.pi_pos (pow_pos (div_pos hPhi (Real.exp_pos 1)) n)

theorem hamiltonian_coprime_even_arithmetic_ratio (n : Nat) [NeZero n] (hn : 3 <= n) :
    (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) /
        hamiltonianCoprimeEvenReference n =
      (hamiltonianCycleSum (hamiltonianCoprimeKernel (n := n)) / 2) /
        (Real.pi * Real.exp (-(n : Real))) := by
  have hPhi : Not ((n.totient : Real) = 0) := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos n)).ne'
  rw [hamiltonian_coprime_even_reference_identity, hamiltonian_coprime_cycle_weight hn]
  field_simp [hPhi, Real.pi_ne_zero, Real.exp_ne_zero]
  <;> ring

theorem hamiltonian_coprime_even_density_sublogarithmic (b : Real) (hb : 0 < b) :
    exists M0 : Nat, 3 <= M0 /\ forall m : Nat, M0 <= m ->
      ((2 * m : Nat) : Real) / ((2 * m).totient : Real) <= b * Real.log (m : Real) := by
  choose M0 hM0 hBudget using hamiltonian_totient_sublogarithmic (b / 2) (by positivity)
  refine Exists.intro M0 (And.intro hM0 ?_)
  intro m hm
  have hm3 : 3 <= m := hM0.trans hm
  have hmR : (0 : Real) < m := by exact_mod_cast (show 0 < m by omega)
  have hm2 : (2 : Real) <= m := by exact_mod_cast (show 2 <= m by omega)
  have hLog2 : Real.log 2 <= Real.log (m : Real) :=
    Real.log_le_log (by norm_num) hm2
  have hSplit : Real.log ((2 * m : Nat) : Real) = Real.log 2 + Real.log (m : Real) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (ne_of_gt hmR)]
  have hDouble : Real.log ((2 * m : Nat) : Real) <= 2 * Real.log (m : Real) := by
    linarith only [hSplit, hLog2]
  calc
    _ <= (b / 2) * Real.log ((2 * m : Nat) : Real) := hBudget (2 * m) (by omega)
    _ <= (b / 2) * (2 * Real.log (m : Real)) :=
      mul_le_mul_of_nonneg_left hDouble (by positivity)
    _ = _ := by ring

theorem hamiltonian_coprime_even_stochastic_count_uniform :
    exists M0 : Nat, 256 <= M0 /\
      forall (m : Nat) [NeZero m], M0 <= m ->
        abs ((hamiltonianCycleSum (hamiltonianCoprimeKernel (n := 2 * m)) / 2) /
          (Real.pi * Real.exp (-2 * (m : Real))) - 1) <=
            2 * (m : Real) ^ (-1 / 2 : Real) := by
  choose N hN hUniform using stochastic_bipartite_sublog_count_uniform.{0}
    (1 / 2) (by norm_num) (by norm_num)
  choose B hB hBudget using hamiltonian_coprime_even_density_sublogarithmic
    (hamiltonianSublogCountDensity (1 / 2)) (hamiltonian_sublog_density_positive _)
  let M0 := max N B
  refine Exists.intro M0 (And.intro (hN.trans (le_max_left _ _)) ?_)
  intro m inst hm
  have hmN : N <= m := (le_max_left _ _).trans hm
  have hmB : B <= m := (le_max_right _ _).trans hm
  have hm1 : 1 <= m := by omega
  have hmR : 0 < (m : Real) := by exact_mod_cast (NeZero.pos m)
  have hPhi : 0 < ((2 * m).totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < 2 * m by omega)
  let a : Real := ((2 * m : Nat) : Real) / ((2 * m).totient : Real)
  have hA1 : 1 <= a := hamiltonian_totient_ratio_ge_one (2 * m) (by omega)
  have hA : a <= hamiltonianSublogCountDensity (1 / 2) * Real.log (m : Real) := hBudget m hmB
  have hq : (Fintype.card (Fin m) : Real) * (1 / (m : Real)) = 1 := by
    rw [Fintype.card_fin]
    field_simp [ne_of_gt hmR]
  have hScale : a * (1 / (m : Real)) = 2 / ((2 * m).totient : Real) := by
    dsimp only [a]
    push_cast
    field_simp [ne_of_gt hmR]
    <;> ring
  have hUpper : forall i j : Fin m,
      hamiltonianCoprimeCrossBlock m i j <= a * (1 / (m : Real)) := by
    intro i j
    rw [hScale]
    calc
      _ <= 1 / ((2 * m).totient : Real) := hamiltonian_coprime_cross_entry_cap m i j
      _ <= 2 / ((2 * m).totient : Real) :=
        div_le_div_of_nonneg_right (by norm_num) hPhi.le
  have hRaw := hUniform (Fin m) (by simpa only [Fintype.card_fin] using hmN)
    (hamiltonianCoprimeCrossBlock m) (1 / (m : Real)) a hq hA1
    (by simpa only [Fintype.card_fin] using hA)
    (hamiltonian_coprime_cross_row_sum m) (hamiltonian_coprime_cross_col_sum m)
    (hamiltonian_coprime_cross_nonnegative m) hUpper (hamiltonian_coprime_cross_physical_gap m)
  have hPi := hamiltonian_bipartite_pi_error_from_factorial (hamiltonianCoprimeCrossBlock m)
    (by simpa only [Fintype.card_fin] using hm1)
    (by simpa only [Fintype.card_fin] using hRaw)
  rw [<- hamiltonian_coprime_cross_cycle_sum] at hPi
  simpa only [Fintype.card_fin] using hPi

theorem hamiltonian_coprime_even_unoriented_half_size_count :
    exists M0 : Nat, 256 <= M0 /\
      forall (m : Nat) [NeZero m], M0 <= m ->
        0 < hamiltonianCoprimeEvenReference (2 * m) /\
        abs ((hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := 2 * m)) : Real) /
          hamiltonianCoprimeEvenReference (2 * m) - 1) <=
            2 * (m : Real) ^ (-1 / 2 : Real) := by
  choose M0 hM0 hCount using hamiltonian_coprime_even_stochastic_count_uniform
  refine Exists.intro M0 (And.intro hM0 ?_)
  intro m inst hm
  refine And.intro (hamiltonian_coprime_even_reference_positive _ (by omega)) ?_
  rw [hamiltonian_coprime_even_arithmetic_ratio (2 * m) (by omega)]
  simpa only [Nat.cast_mul, Nat.cast_ofNat, neg_mul] using hCount m hm

end PrimeFactorOscillations
