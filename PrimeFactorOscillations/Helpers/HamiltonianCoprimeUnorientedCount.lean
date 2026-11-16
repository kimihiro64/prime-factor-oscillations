/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeAperiodicCount
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeConstant
import PrimeFactorOscillations.Helpers.HamiltonianGraphEntropyGauge

/-! # The actual unoriented odd coprime-circle count

The common edge weight and the reversal factor are restored exactly.
The reference uses the explicit arithmetic divisor-product constant.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCoprimeUnorientedReference (n : Nat) : Real :=
  (((n - 1).factorial : Real) / (2 * (n : Real) ^ n)) *
    (n.totient : Real) ^ n * hamiltonianCoprimeArithmeticConstant n

variable {n : Nat} [NeZero n]

theorem hamiltonian_coprime_cycle_weight (hn : 3 <= n) :
    hamiltonianCycleSum (hamiltonianCoprimeKernel (n := n)) =
      (2 * (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real)) /
        (n.totient : Real) ^ n := by
  have hScale :
      hamiltonianCycleSum (hamiltonianCoprimeKernel (n := n)) =
        hamiltonianCycleSum (hamiltonianCoprimeAdjacency (n := n)) / (n.totient : Real) ^ n := by
    unfold hamiltonianCycleSum
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro f hf
    by_cases hCycle : (hamiltonianPermutationOrbits f).card = 1
    case pos =>
      simp only [hCycle, ite_true, hamiltonianCoprimeKernel,
        Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ZMod.card]
    case neg => simp only [hCycle, ite_false, zero_div]
  have hCount :
      hamiltonianCycleSum (hamiltonianCoprimeAdjacency (n := n)) =
        2 * (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) := by
    have hAdj : hamiltonianCoprimeAdjacency (n := n) =
        (fun x y : ZMod n => if hamiltonianCoprimeRelation x y then (1 : Real) else 0) := by
      ext x y
      by_cases h : IsUnit (x - y)
      case pos => simp only [hamiltonianCoprimeAdjacency, hamiltonianCoprimeRelation, h, ite_true]
      case neg => simp only [hamiltonianCoprimeAdjacency, hamiltonianCoprimeRelation, h, ite_false]
    rw [hAdj, hamiltonian_indicator_cycle_count]
    have hSym : forall x y : ZMod n,
        hamiltonianCoprimeRelation x y -> hamiltonianCoprimeRelation y x :=
      hamiltonian_coprime_relation_symmetric
    have hExact := hamiltonian_unoriented_cycle_card
      (hamiltonianCoprimeRelation (n := n)) hSym
      (by simpa only [ZMod.card] using hn)
    have hReal := congrArg (fun v : Nat => (v : Real)) hExact
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hamiltonianGraphUnorientedCount] using hReal
  rw [hScale, hCount]

theorem hamiltonian_coprime_odd_reference_constant (hOdd : Odd n) :
    hamiltonianAperiodicCycleReference (hamiltonianCoprimeKernel (n := n))
      (1 / (n : Real)) =
      (((n - 1).factorial : Real) / (n : Real) ^ n) *
        hamiltonianCoprimeArithmeticConstant n := by
  unfold hamiltonianAperiodicCycleReference
  rw [ZMod.card, mul_assoc, hamiltonian_coprime_odd_gram_factor_constant hOdd]

theorem hamiltonian_coprime_odd_unoriented_reference (hOdd : Odd n) :
    hamiltonianCoprimeUnorientedReference n =
      ((n.totient : Real) ^ n / 2) *
        hamiltonianAperiodicCycleReference (hamiltonianCoprimeKernel (n := n))
          (1 / (n : Real)) := by
  rw [hamiltonian_coprime_odd_reference_constant hOdd]
  unfold hamiltonianCoprimeUnorientedReference
  ring

theorem hamiltonian_coprime_odd_unoriented_ratio (hn : 3 <= n) (hOdd : Odd n)
    (hRef : Not (hamiltonianAperiodicCycleReference (hamiltonianCoprimeKernel (n := n))
      (1 / (n : Real)) = 0)) :
    (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) /
        hamiltonianCoprimeUnorientedReference n =
      hamiltonianCycleSum (hamiltonianCoprimeKernel (n := n)) /
        hamiltonianAperiodicCycleReference (hamiltonianCoprimeKernel (n := n))
          (1 / (n : Real)) := by
  have hPhi : Not ((n.totient : Real) = 0) := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos n)).ne'
  rw [hamiltonian_coprime_odd_unoriented_reference hOdd, hamiltonian_coprime_cycle_weight hn]
  field_simp
  <;> ring

theorem hamiltonian_coprime_odd_unoriented_count_uniform :
    exists N0 : Nat, 256 <= N0 /\
      forall (n : Nat) [NeZero n], N0 <= n -> Odd n ->
        0 < hamiltonianCoprimeUnorientedReference n /\
        abs ((hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) /
          hamiltonianCoprimeUnorientedReference n - 1) <=
            17 * (n : Real) ^ (-(1 : Real) / 10) := by
  choose N0 hN0 hCount using hamiltonian_coprime_odd_count_uniform
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n inst hn hOdd
  have hRaw := hCount n hn hOdd
  have hn3 : 3 <= n := by omega
  have hPhi : 0 < (n.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos n)
  have hRef : 0 < hamiltonianCoprimeUnorientedReference n := by
    rw [hamiltonian_coprime_odd_unoriented_reference hOdd]
    exact mul_pos (div_pos (pow_pos hPhi _) (by norm_num)) hRaw.1
  refine And.intro hRef ?_
  rw [hamiltonian_coprime_odd_unoriented_ratio hn3 hOdd (ne_of_gt hRaw.1)]
  exact hRaw.2

end PrimeFactorOscillations
