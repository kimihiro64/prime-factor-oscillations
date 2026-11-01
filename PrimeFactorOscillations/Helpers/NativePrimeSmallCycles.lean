/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.SplitIfs
import PrimeFactorOscillations.Helpers.NativePrimeVertexGapIncidence

/-! # The first possible even-sized native cycle has four edges

Strict undirected edges are represented once, with their smaller endpoint
first. Two distinct such edges cannot give even degree at both endpoints.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_cycle_degree_eq_sum (C : Finset (Prod Nat Nat)) (p : Nat) :
    nativePrimeVertexCycleDegree C p =
      C.sum (fun e => (if e.1 = p then 1 else 0) + (if e.2 = p then 1 else 0)) := by
  simp [nativePrimeVertexCycleDegree, Finset.sum_add_distrib, Finset.sum_boole]

theorem native_even_cycle_card_ne_two (P : Finset Nat) (C : Finset (Prod Nat Nat))
    (hC : C <= nativePrimeVertexEdges P)
    (heven : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0) :
    Not (C.card = 2) := by
  intro htwo
  choose e he using Finset.card_eq_two.mp htwo
  choose f hf using he
  have hneq : Not (e = f) := hf.1
  have hCeq : C = {e, f} := hf.2
  have heC : Membership.mem C e := by simp [hCeq]
  have hfC : Membership.mem C f := by simp [hCeq]
  have hed := (native_gap_edges_mem_iff P e).mp (hC heC)
  have hfd := (native_gap_edges_mem_iff P f).mp (hC hfC)
  have hd1 := heven e.1 hed.1
  have hd2 := heven e.2 hed.2.1
  have henot : Not (Membership.mem ({f} : Finset (Prod Nat Nat)) e) := by
    simpa only [Finset.mem_singleton] using hneq
  rw [native_cycle_degree_eq_sum, hCeq, Finset.sum_insert henot, Finset.sum_singleton] at hd1 hd2
  have hdifferent : Not (And (e.1 = f.1) (e.2 = f.2)) := by
    intro h
    exact hneq (Prod.ext h.1 h.2)
  split_ifs at hd1 hd2 <;> omega

theorem native_small_even_cycle_empty (P : Finset Nat) (C : Finset (Prod Nat Nat))
    (hC : C <= nativePrimeVertexEdges P)
    (heven : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hsize : C.card <= 3) (hcardeven : C.card % 2 = 0) : C = {} := by
  by_cases hz : C = {}
  . exact hz
  . have hpos : 0 < C.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
    have htwo : C.card = 2 := by omega
    exact False.elim (native_even_cycle_card_ne_two P C hC heven htwo)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
