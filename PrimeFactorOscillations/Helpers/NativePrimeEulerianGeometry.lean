/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NativePrimeFourCycle
import PrimeFactorOscillations.Helpers.NativePrimePhaseCycles

/-! # Complete Eulerian masks on the first phase-sensitive prime graphs -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_phase_eulerian_card_ne_one (P : Finset Nat)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P)
    (heven : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0) :
    Not (C.card = 1) := by
  intro hone
  choose e heq using Finset.card_eq_one.mp hone
  have heC : Membership.mem C e := by rw [heq]; simp
  have hed := (native_gap_edges_mem_iff P e).mp (hC heC)
  have hd := heven e.1 hed.1
  rw [native_cycle_degree_eq_sum, heq, Finset.sum_singleton] at hd
  have hn : Not (e.2 = e.1) := hed.2.2.ne'
  simp [hn] at hd

theorem native_phase_small_eulerian_empty (P : Finset Nat)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P)
    (heven : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hc : C.card <= 2) : C = {} := by
  by_cases hz : C = {}
  . exact hz
  . have hp : 0 < C.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
    have h1 := native_phase_eulerian_card_ne_one P C hC heven
    have h2 := native_even_cycle_card_ne_two P C hC heven
    omega

theorem native_phase_eulerian_masks_small (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hc : G.card <= 2) :
    nativeEulerianMasks P G = {({} : Finset (Prod Nat Nat))} := by
  ext C
  rw [native_eulerian_masks_mem_iff, Finset.mem_singleton]
  constructor
  . intro h
    exact native_phase_small_eulerian_empty P C (h.1.trans hG) h.2
      ((Finset.card_le_card h.1).trans hc)
  . intro h
    rw [h]
    exact And.intro (Finset.empty_subset G) (by simp [nativePrimeVertexCycleDegree])

theorem native_phase_eulerian_count_small (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hc : G.card <= 2) :
    nativeEulerianCount P G = 1 := by
  unfold nativeEulerianCount
  rw [native_phase_eulerian_masks_small P G hG hc, Finset.card_singleton]

theorem native_phase_triangle_support (P : Finset Nat) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hpq : p < q) (hqr : q < r) :
    ({(p, q), (q, r), (p, r)} : Finset (Prod Nat Nat)) <= nativePrimeVertexEdges P := by
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  . exact (native_gap_edges_mem_iff P (p, q)).mpr (And.intro hp (And.intro hq hpq))
  . exact (native_gap_edges_mem_iff P (q, r)).mpr (And.intro hq (And.intro hr hqr))
  . exact (native_gap_edges_mem_iff P (p, r)).mpr
      (And.intro hp (And.intro hr (lt_trans hpq hqr)))

theorem native_phase_triangle_card (p q r : Nat) (hpq : p < q) (hqr : q < r) :
    ({(p, q), (q, r), (p, r)} : Finset (Prod Nat Nat)).card = 3 := by
  simp [hpq.ne, hpq.ne', hqr.ne]

theorem native_phase_triangle_degrees_even (p q r : Nat) (hpq : p < q) (hqr : q < r)
    (x : Nat) :
    nativePrimeVertexCycleDegree {(p, q), (q, r), (p, r)} x % 2 = 0 := by
  have h1 : Not (Membership.mem ({(q, r), (p, r)} : Finset (Prod Nat Nat)) (p, q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  have h2 : Not (Membership.mem ({(p, r)} : Finset (Prod Nat Nat)) (q, r)) := by
    simp only [Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [native_cycle_degree_eq_sum, Finset.sum_insert h1, Finset.sum_insert h2,
    Finset.sum_singleton]
  dsimp only
  split_ifs <;> omega

theorem native_phase_triangle_eulerian_masks (P : Finset Nat) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hpq : p < q) (hqr : q < r) :
    nativeEulerianMasks P {(p, q), (q, r), (p, r)} =
      {({} : Finset (Prod Nat Nat)), {(p, q), (q, r), (p, r)}} := by
  have hT := native_phase_triangle_support P p q r hp hq hr hpq hqr
  have hcT := native_phase_triangle_card p q r hpq hqr
  ext C
  rw [native_eulerian_masks_mem_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  . intro h
    by_cases hz : C = {}
    . exact Or.inl hz
    . have hpos : 0 < C.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
      have hle := Finset.card_le_card h.1
      have h1 := native_phase_eulerian_card_ne_one P C (h.1.trans hT) h.2
      have h2 := native_even_cycle_card_ne_two P C (h.1.trans hT) h.2
      have hback : ({(p, q), (q, r), (p, r)} : Finset (Prod Nat Nat)).card <= C.card := by
        omega
      exact Or.inr (Finset.eq_of_subset_of_card_le h.1 hback)
  . intro h
    rcases h with h | h
    . rw [h]
      exact And.intro (Finset.empty_subset _) (by simp [nativePrimeVertexCycleDegree])
    . rw [h]
      exact And.intro (Finset.Subset.refl _)
        (fun x _ => native_phase_triangle_degrees_even p q r hpq hqr x)

theorem native_phase_triangle_eulerian_count (P : Finset Nat) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hpq : p < q) (hqr : q < r) :
    nativeEulerianCount P {(p, q), (q, r), (p, r)} = 2 := by
  have hn : Not (({(p, q), (q, r), (p, r)} : Finset (Prod Nat Nat)) = {}) := by
    intro h
    have hc := native_phase_triangle_card p q r hpq hqr
    rw [h, Finset.card_empty] at hc
    omega
  unfold nativeEulerianCount
  rw [native_phase_triangle_eulerian_masks P p q r hp hq hr hpq hqr]
  exact Finset.card_pair (Ne.symm hn)

theorem native_phase_four_cycle_opposite_degree_sum (p q r s : Nat)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeFourCycle p q r s) :
    nativePrimeVertexCycleDegree C p + nativePrimeVertexCycleDegree C r = C.card := by
  have hpr := lt_trans hpq hqr
  have hps := lt_trans hpq (lt_trans hqr hrs)
  rw [native_cycle_degree_eq_sum, native_cycle_degree_eq_sum, <- Finset.sum_add_distrib]
  calc
    _ = C.sum (fun _ => (1 : Nat)) := by
      apply Finset.sum_congr rfl
      intro e he
      have hh := hC he
      simp only [nativePrimeFourCycle, Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl | rfl <;>
        simp [hpq.ne', hqr.ne, hrs.ne', hpr.ne, hpr.ne', hps.ne']
    _ = C.card := by simp

theorem native_phase_four_cycle_eulerian_masks (P : Finset Nat) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    nativeEulerianMasks P (nativePrimeFourCycle p q r s) =
      {({} : Finset (Prod Nat Nat)), nativePrimeFourCycle p q r s} := by
  have hT := native_four_cycle_support P p q r s hp hq hr hs hpq hqr hrs
  have hcT := native_four_cycle_card p q r s hpq hqr hrs
  ext C
  rw [native_eulerian_masks_mem_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  . intro h
    have hd := native_phase_four_cycle_opposite_degree_sum p q r s hpq hqr hrs C h.1
    have hdp := h.2 p hp
    have hdr := h.2 r hr
    have heven : C.card % 2 = 0 := by omega
    by_cases hz : C = {}
    . exact Or.inl hz
    . have hnot : Not (C.card <= 3) := fun hc =>
        hz (native_small_even_cycle_empty P C (h.1.trans hT) h.2 hc heven)
      have hle := Finset.card_le_card h.1
      have hback : (nativePrimeFourCycle p q r s).card <= C.card := by omega
      exact Or.inr (Finset.eq_of_subset_of_card_le h.1 hback)
  . intro h
    rcases h with h | h
    . rw [h]
      exact And.intro (Finset.empty_subset _) (by simp [nativePrimeVertexCycleDegree])
    . rw [h]
      exact And.intro (Finset.Subset.refl _)
        (fun x _ => native_four_cycle_degrees_even p q r s hpq hqr hrs x)

theorem native_phase_four_cycle_eulerian_count (P : Finset Nat) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    nativeEulerianCount P (nativePrimeFourCycle p q r s) = 2 := by
  have hn : Not (nativePrimeFourCycle p q r s = {}) := by
    intro h
    have hc := native_four_cycle_card p q r s hpq hqr hrs
    rw [h, Finset.card_empty] at hc
    omega
  unfold nativeEulerianCount
  rw [native_phase_four_cycle_eulerian_masks P p q r s hp hq hr hs hpq hqr hrs]
  exact Finset.card_pair (Ne.symm hn)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
