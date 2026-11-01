/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NativePrimeVertexGapPartition
import PrimeFactorOscillations.Mathlib.Data.Nat.SquareProductSupport

/-! # Full squareclass-independent prime insertion

A prime larger than every old coordinate cannot occur in a square relation.
Every other new relation is exactly a fixed old product times a nonempty
product of new gaps; no relation is discarded by a pairwise test.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_gap_new_vertex_excluded (P : Finset Nat) (q : Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hq : Nat.Prime q)
    (hlarge : forall p : Nat, Membership.mem P p -> p < q)
    (S : Finset (Sum Nat (Prod Nat Nat)))
    (hS : S <= nativeVertexGapBasis (insert q P))
    (hsq : IsSquare (S.prod nativeVertexGapValue)) :
    Not (Membership.mem S (Sum.inl q)) := by
  classical
  intro hv
  let O := Inter.inter S (nativeVertexGapBasis P)
  let T := P.filter (fun p => Membership.mem S (Sum.inr (p, q)))
  have hO : O <= nativeVertexGapBasis P := Finset.inter_subset_right
  have hT : T <= P := Finset.filter_subset _ _
  have hnoO : Not (Dvd.dvd q (O.prod nativeVertexGapValue)) := by
    intro hd
    cases (_root_.Prime.dvd_finsetProd_iff hq.prime nativeVertexGapValue).mp hd with
    | intro x hx =>
      exact (Nat.not_le_of_lt (native_gap_basis_value_lt P q hlarge x (hO hx.1)))
        (Nat.le_of_dvd (native_gap_basis_value_positive P hP x (hO hx.1)) hx.2)
  have hnoT : Not (Dvd.dvd q (T.prod (fun p => q - p))) := by
    intro hd
    cases (_root_.Prime.dvd_finsetProd_iff hq.prime (fun p => q - p)).mp hd with
    | intro p hp =>
      have hpP := hT hp.1
      have hppos := (hP p hpP).pos
      have hpq := hlarge p hpP
      have hpos : 0 < q - p := Nat.sub_pos_of_lt hpq
      have hlt : q - p < q := by omega
      exact (Nat.not_le_of_lt hlt) (Nat.le_of_dvd hpos hp.2)
  have hno : Not (Dvd.dvd q (T.prod (fun p => q - p) * O.prod nativeVertexGapValue)) := by
    intro hd
    exact (hq.dvd_mul.mp hd).elim hnoT hnoO
  have hpos : 0 < T.prod (fun p => q - p) * O.prod nativeVertexGapValue := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hno
    rw [hz]
    exact dvd_zero q
  have hsq' : IsSquare (q * (T.prod (fun p => q - p) * O.prod nativeVertexGapValue)) := by
    rw [native_gap_relation_product_partition P S,
      native_gap_new_part_product P q hlarge S hS] at hsq
    simpa [hv, Nat.mul_assoc, O, T] using hsq
  exact hno (Nat.squarefree_dvd_of_positive_square_product hq.pos hpos hq.squarefree hsq')

theorem native_gap_independent_insert (P : Finset Nat) (q : Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hq : Nat.Prime q)
    (hlarge : forall p : Nat, Membership.mem P p -> p < q)
    (hind : nativePrimeVertexGapIndependent P)
    (hclear : forall O : Finset (Sum Nat (Prod Nat Nat)),
      O <= nativeVertexGapBasis P -> forall T : Finset Nat, T <= P ->
      T.Nonempty -> Not (IsSquare (O.prod nativeVertexGapValue *
        T.prod (fun p => q - p)))) :
    nativePrimeVertexGapIndependent (insert q P) := by
  classical
  intro S hS hsq
  have hsub := Finset.mem_powerset.mp hS
  have hv := native_gap_new_vertex_excluded P q hP hq hlarge S hsub hsq
  let O := Inter.inter S (nativeVertexGapBasis P)
  let T := P.filter (fun p => Membership.mem S (Sum.inr (p, q)))
  have hOsub : O <= nativeVertexGapBasis P := Finset.inter_subset_right
  have hTsub : T <= P := Finset.filter_subset _ _
  have hsqOT : IsSquare (O.prod nativeVertexGapValue * T.prod (fun p => q - p)) := by
    rw [native_gap_relation_product_partition P S,
      native_gap_new_part_product P q hlarge S hsub] at hsq
    simpa [hv, O, T, Nat.mul_comm] using hsq
  by_cases hTempty : T = {}
  case neg =>
    exact False.elim (hclear O hOsub T hTsub
      (Finset.nonempty_iff_ne_empty.mpr hTempty) hsqOT)
  case pos =>
    have hsqO : IsSquare (O.prod nativeVertexGapValue) := by
      simpa [hTempty] using hsqOT
    have hOempty : O = {} := hind O (Finset.mem_powerset.mpr hOsub) hsqO
    exact native_gap_relation_empty_of_parts P q hlarge S hsub hOempty hTempty hv

end PrimeFactorOscillations.FiniteFieldIntegerSignature
