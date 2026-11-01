/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeVertexGapGreedy
import PrimeFactorOscillations.Helpers.NativePrimeVertexGapGeometry

/-! # Elementary invariants of full squareclass selection -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_prime_gap_insert_subset (P : Finset Nat) (q : Nat) :
    nativePrimeVertexGapGreedyInsert P q <= insert q P := by
  unfold nativePrimeVertexGapGreedyInsert
  split
  . exact le_refl _
  . intro p hp
    exact Finset.mem_insert_of_mem hp

theorem native_prime_gap_insert_contains (P : Finset Nat) (q : Nat) :
    P <= nativePrimeVertexGapGreedyInsert P q := by
  unfold nativePrimeVertexGapGreedyInsert
  split
  . intro p hp
    exact Finset.mem_insert_of_mem hp
  . exact le_refl _

theorem native_gap_independent_mono {P Q : Finset Nat} (hPQ : P <= Q)
    (hind : nativePrimeVertexGapIndependent Q) : nativePrimeVertexGapIndependent P := by
  intro S hS hsq
  exact hind S (Finset.mem_powerset.mpr
    ((Finset.mem_powerset.mp hS).trans (native_gap_basis_monotone hPQ))) hsq

end PrimeFactorOscillations.FiniteFieldIntegerSignature
