/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeFourCycle
import PrimeFactorOscillations.Helpers.NativePrimeSmallCycles

/-! # Four arbitrary increasing vertices give an even four-edge cycle -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_four_cycle_support (P : Finset Nat) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    nativePrimeFourCycle p q r s <= nativePrimeVertexEdges P := by
  intro e he
  simp only [nativePrimeFourCycle, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  . exact (native_gap_edges_mem_iff P (p, q)).mpr (And.intro hp (And.intro hq hpq))
  . exact (native_gap_edges_mem_iff P (q, r)).mpr (And.intro hq (And.intro hr hqr))
  . exact (native_gap_edges_mem_iff P (r, s)).mpr (And.intro hr (And.intro hs hrs))
  . exact (native_gap_edges_mem_iff P (p, s)).mpr
      (And.intro hp (And.intro hs (lt_trans hpq (lt_trans hqr hrs))))

theorem native_four_cycle_card (p q r s : Nat)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    (nativePrimeFourCycle p q r s).card = 4 := by
  have hpr : p < r := lt_trans hpq hqr
  have hqs : q < s := lt_trans hqr hrs
  simp [nativePrimeFourCycle, hpq.ne, hpq.ne', hpr.ne, hpr.ne',
    hqr.ne, hqs.ne, hrs.ne]

theorem native_four_cycle_degrees_even (p q r s : Nat)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) (x : Nat) :
    nativePrimeVertexCycleDegree (nativePrimeFourCycle p q r s) x % 2 = 0 := by
  have h1 : Not (Membership.mem ({(q, r), (r, s), (p, s)} :
      Finset (Prod Nat Nat)) (p, q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  have h2 : Not (Membership.mem ({(r, s), (p, s)} :
      Finset (Prod Nat Nat)) (q, r)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  have h3 : Not (Membership.mem ({(p, s)} : Finset (Prod Nat Nat)) (r, s)) := by
    simp only [Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [native_cycle_degree_eq_sum, nativePrimeFourCycle,
    Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_singleton]
  dsimp only
  split_ifs <;> omega
end PrimeFactorOscillations.FiniteFieldIntegerSignature
