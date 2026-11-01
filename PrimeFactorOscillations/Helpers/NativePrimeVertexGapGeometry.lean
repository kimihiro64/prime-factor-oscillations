/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeVertexGapIndependent

/-! # Geometry of the complete indexed vertex/gap basis

These support and positivity facts enter the full insertion partition and
the arbitrary-degree rejection consumer.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_gap_basis_vertex_mem (P : Finset Nat) (p : Nat) :
    Membership.mem (nativeVertexGapBasis P) (Sum.inl p) <-> Membership.mem P p := by
  simp [nativeVertexGapBasis]

theorem native_gap_basis_edge_mem (P : Finset Nat) (p q : Nat) :
    Membership.mem (nativeVertexGapBasis P) (Sum.inr (p, q)) <->
      And (Membership.mem P p) (And (Membership.mem P q) (p < q)) := by
  simp [nativeVertexGapBasis, and_assoc]

theorem native_gap_basis_value_positive (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (x : Sum Nat (Prod Nat Nat)) (hx : Membership.mem (nativeVertexGapBasis P) x) :
    0 < nativeVertexGapValue x := by
  cases x with
  | inl p =>
    exact (hP p ((native_gap_basis_vertex_mem P p).mp hx)).pos
  | inr pq =>
    cases pq with
    | mk p q =>
      exact Nat.sub_pos_of_lt ((native_gap_basis_edge_mem P p q).mp hx).2.2

theorem native_gap_subfamily_product_positive (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (S : Finset (Sum Nat (Prod Nat Nat))) (hS : S <= nativeVertexGapBasis P) :
    0 < S.prod nativeVertexGapValue := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    rw [Finset.prod_insert hx]
    exact Nat.mul_pos
      (native_gap_basis_value_positive P hP x (hS (Finset.mem_insert_self x S)))
      (ih (fun y hy => hS (Finset.mem_insert_of_mem hy)))

theorem native_gap_basis_value_lt (P : Finset Nat) (Q : Nat)
    (hP : forall p : Nat, Membership.mem P p -> p < Q)
    (x : Sum Nat (Prod Nat Nat)) (hx : Membership.mem (nativeVertexGapBasis P) x) :
    nativeVertexGapValue x < Q := by
  cases x with
  | inl p =>
    exact hP p ((native_gap_basis_vertex_mem P p).mp hx)
  | inr pq =>
    cases pq with
    | mk p q =>
      have hh := (native_gap_basis_edge_mem P p q).mp hx
      exact (Nat.sub_le q p).trans_lt (hP q hh.2.1)

theorem native_gap_independent_empty : nativePrimeVertexGapIndependent {} := by
  intro S hS _
  have hsub : S <= nativeVertexGapBasis {} := Finset.mem_powerset.mp hS
  have heq : nativeVertexGapBasis {} = {} := by simp [nativeVertexGapBasis]
  rw [heq] at hsub
  apply Finset.Subset.antisymm hsub
  intro x hx
  simp at hx

theorem native_gap_basis_monotone {P Q : Finset Nat} (hPQ : P <= Q) :
    nativeVertexGapBasis P <= nativeVertexGapBasis Q := by
  intro x hx
  cases x with
  | inl p =>
    exact (native_gap_basis_vertex_mem Q p).mpr
      (hPQ ((native_gap_basis_vertex_mem P p).mp hx))
  | inr pq =>
    cases pq with
    | mk p q =>
      have hh := (native_gap_basis_edge_mem P p q).mp hx
      exact (native_gap_basis_edge_mem Q p q).mpr
        (And.intro (hPQ hh.1) (And.intro (hPQ hh.2.1) hh.2.2))

end PrimeFactorOscillations.FiniteFieldIntegerSignature
