/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeCycleRows
import PrimeFactorOscillations.Helpers.NativePrimeVertexGapParity

/-! # Exact incidence exponents of the lower and upper native rows -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_gap_edges_mem_iff (P : Finset Nat) (e : Prod Nat Nat) :
    Membership.mem (nativePrimeVertexEdges P) e <->
      And (Membership.mem P e.1) (And (Membership.mem P e.2) (e.1 < e.2)) := by
  simp [nativePrimeVertexEdges, and_assoc]

theorem native_gap_row_multiplicity_vertex (A B : Finset (Prod Nat Nat)) (p : Nat) :
    nativeVertexGapRowMultiplicity A B (Sum.inl p) =
      (A.filter (fun e => e.1 = p)).card + (B.filter (fun e => e.2 = p)).card := by
  simp [nativeVertexGapRowMultiplicity]

theorem native_gap_row_multiplicity_edge (A B : Finset (Prod Nat Nat))
    (e : Prod Nat Nat) :
    nativeVertexGapRowMultiplicity A B (Sum.inr e) =
      (if Membership.mem A e then 1 else 0) + (if Membership.mem B e then 1 else 0) := by
  have hf : forall C : Finset (Prod Nat Nat),
      (C.filter (fun x => x = e)).card = (if Membership.mem C e then 1 else 0) := by
    intro C
    by_cases hm : Membership.mem C e
    case pos =>
      have heq : C.filter (fun x => x = e) = {e} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        . intro hx
          exact hx.2
        . intro hx
          subst x
          exact And.intro hm rfl
      rw [heq]
      simp [hm]
    case neg =>
      have heq : C.filter (fun x => x = e) = {} := by
        refine Finset.Subset.antisymm ?_ (by intro x hx; simp at hx)
        intro x hx
        exfalso
        have hh := Finset.mem_filter.mp hx
        have hxe := hh.2
        rw [hxe] at hh
        exact hm hh.1
      rw [heq]
      simp [hm]
  have hh : (A.filter (fun x => x = e)).card + (B.filter (fun x => x = e)).card =
      (if Membership.mem A e then 1 else 0) + (if Membership.mem B e then 1 else 0) := by
    rw [hf A, hf B]
  simpa [nativeVertexGapRowMultiplicity] using hh

theorem native_gap_mapped_product {I : Type*} (P : Finset Nat) (A : Finset I)
    (f : I -> Sum Nat (Prod Nat Nat))
    (hmap : forall i : I, Membership.mem A i -> Membership.mem (nativeVertexGapBasis P) (f i)) :
    A.prod (fun i => nativeVertexGapValue (f i)) =
      (nativeVertexGapBasis P).prod (fun x => nativeVertexGapValue x ^
        (A.filter (fun i => f i = x)).card) := by
  classical
  symm
  calc
    _ = (nativeVertexGapBasis P).prod (fun x =>
        (A.filter (fun i => f i = x)).prod (fun i => nativeVertexGapValue (f i))) := by
      apply Finset.prod_congr rfl
      intro x _
      rw [<- Finset.prod_const]
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.prod_fiberwise_of_maps_to hmap (fun i => nativeVertexGapValue (f i))

theorem native_gap_row_product_powers (P : Finset Nat) (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    A.prod (fun e => e.1 * (e.2 - e.1)) *
        B.prod (fun e => e.2 * (e.2 - e.1)) =
      (nativeVertexGapBasis P).prod (fun x =>
        nativeVertexGapValue x ^ nativeVertexGapRowMultiplicity A B x) := by
  classical
  have hlA : forall e : Prod Nat Nat, Membership.mem A e ->
      Membership.mem (nativeVertexGapBasis P) (Sum.inl e.1) := by
    intro e he
    exact (native_gap_basis_vertex_mem P e.1).mpr ((native_gap_edges_mem_iff P e).mp (hA he)).1
  have huB : forall e : Prod Nat Nat, Membership.mem B e ->
      Membership.mem (nativeVertexGapBasis P) (Sum.inl e.2) := by
    intro e he
    exact (native_gap_basis_vertex_mem P e.2).mpr ((native_gap_edges_mem_iff P e).mp (hB he)).2.1
  have hgA : forall e : Prod Nat Nat, Membership.mem A e ->
      Membership.mem (nativeVertexGapBasis P) (Sum.inr e) := by
    intro e he
    exact (native_gap_basis_edge_mem P e.1 e.2).mpr ((native_gap_edges_mem_iff P e).mp (hA he))
  have hgB : forall e : Prod Nat Nat, Membership.mem B e ->
      Membership.mem (nativeVertexGapBasis P) (Sum.inr e) := by
    intro e he
    exact (native_gap_basis_edge_mem P e.1 e.2).mpr ((native_gap_edges_mem_iff P e).mp (hB he))
  change A.prod (fun e => nativeVertexGapValue (Sum.inl e.1) *
      nativeVertexGapValue (Sum.inr e)) *
    B.prod (fun e => nativeVertexGapValue (Sum.inl e.2) *
      nativeVertexGapValue (Sum.inr e)) = _
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [native_gap_mapped_product P A (fun e => Sum.inl e.1) hlA,
    native_gap_mapped_product P A (fun e => Sum.inr e) hgA,
    native_gap_mapped_product P B (fun e => Sum.inl e.2) huB,
    native_gap_mapped_product P B (fun e => Sum.inr e) hgB]
  rw [<- Finset.prod_mul_distrib, <- Finset.prod_mul_distrib, <- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x _
  simp only [nativeVertexGapRowMultiplicity, pow_add]

end PrimeFactorOscillations.FiniteFieldIntegerSignature
