/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NativePrimeVertexGapIncidence

/-! # Exact cycle kernel of the native lower and upper row square products

Every edge must occur in both row selections or neither. The remaining
vertex exponents are exactly the degrees of that common edge set.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_gap_row_product_square_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    IsSquare (A.prod (fun e => e.1 * (e.2 - e.1)) *
      B.prod (fun e => e.2 * (e.2 - e.1))) <->
        And (A = B) (forall p : Nat, Membership.mem P p ->
          nativePrimeVertexCycleDegree A p % 2 = 0) := by
  classical
  rw [native_gap_row_product_powers P A B hA hB,
    native_gap_square_power_product_iff P hP hind (nativeVertexGapBasis P)
      (le_refl _) (nativeVertexGapRowMultiplicity A B)]
  constructor
  case mp =>
    intro hpar
    have hAB : A = B := by
      apply Finset.Subset.antisymm
      . intro e he
        by_contra hnot
        have hedge := (native_gap_edges_mem_iff P e).mp (hA he)
        have hz := hpar (Sum.inr e) ((native_gap_basis_edge_mem P e.1 e.2).mpr hedge)
        rw [native_gap_row_multiplicity_edge] at hz
        simp [he, hnot] at hz
      . intro e he
        by_contra hnot
        have hedge := (native_gap_edges_mem_iff P e).mp (hB he)
        have hz := hpar (Sum.inr e) ((native_gap_basis_edge_mem P e.1 e.2).mpr hedge)
        rw [native_gap_row_multiplicity_edge] at hz
        simp [he, hnot] at hz
    refine And.intro hAB ?_
    intro p hp
    have hz := hpar (Sum.inl p) ((native_gap_basis_vertex_mem P p).mpr hp)
    rw [native_gap_row_multiplicity_vertex, <- hAB] at hz
    exact hz
  case mpr =>
    intro h
    have hAB := h.1
    have hdeg := h.2
    subst B
    intro x hx
    cases x with
    | inl p =>
      simpa only [native_gap_row_multiplicity_vertex, nativePrimeVertexCycleDegree] using
        hdeg p ((native_gap_basis_vertex_mem P p).mp hx)
    | inr e =>
      rw [native_gap_row_multiplicity_edge]
      by_cases he : Membership.mem A e <;> simp [he]

end PrimeFactorOscillations.FiniteFieldIntegerSignature
