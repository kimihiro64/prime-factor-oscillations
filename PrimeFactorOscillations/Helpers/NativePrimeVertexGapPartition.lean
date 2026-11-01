/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NativePrimeVertexGapGeometry

/-! # Exact insertion partition of the indexed vertex/gap basis

A selected relation splits into old coordinates, the new prime coordinate,
and selected gaps to the new vertex. The indices remain distinct throughout.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_gap_new_vertex_not_mem (P : Finset Nat) (q : Nat)
    (hlarge : forall p : Nat, Membership.mem P p -> p < q) :
    Not (Membership.mem P q) := by
  intro hq
  exact (Nat.lt_irrefl q) (hlarge q hq)

theorem native_gap_new_part_erase (P : Finset Nat) (q : Nat)
    (hlarge : forall p : Nat, Membership.mem P p -> p < q)
    (S : Finset (Sum Nat (Prod Nat Nat)))
    (hS : S <= nativeVertexGapBasis (insert q P)) :
    (S \ nativeVertexGapBasis P).erase (Sum.inl q) =
      (P.filter (fun p => Membership.mem S (Sum.inr (p, q)))).image
        (fun p => (Sum.inr (p, q) : Sum Nat (Prod Nat Nat))) := by
  classical
  have hq := native_gap_new_vertex_not_mem P q hlarge
  ext x
  cases x with
  | inl p =>
    constructor
    case mp =>
      intro hx
      have he := Finset.mem_erase.mp hx
      have hd := Finset.mem_sdiff.mp he.2
      have hp := (native_gap_basis_vertex_mem (insert q P) p).mp (hS hd.1)
      cases Finset.mem_insert.mp hp with
      | inl hpq =>
        subst p
        exact False.elim (he.1 rfl)
      | inr hpP =>
        exact False.elim (hd.2 ((native_gap_basis_vertex_mem P p).mpr hpP))
    case mpr =>
      intro hx
      cases Finset.mem_image.mp hx with
      | intro r hr =>
        cases hr.2
  | inr pr =>
    cases pr with
    | mk p r =>
      constructor
      case mp =>
        intro hx
        have hd := Finset.mem_sdiff.mp (Finset.mem_erase.mp hx).2
        have hpr := (native_gap_basis_edge_mem (insert q P) p r).mp (hS hd.1)
        have hpP : Membership.mem P p := by
          cases Finset.mem_insert.mp hpr.1 with
          | inr hpP => exact hpP
          | inl hpq =>
            subst p
            cases Finset.mem_insert.mp hpr.2.1 with
            | inl hrq =>
              subst r
              exact False.elim ((Nat.lt_irrefl q) hpr.2.2)
            | inr hrP =>
              exact False.elim ((Nat.lt_asymm hpr.2.2) (hlarge r hrP))
        have hrq : r = q := by
          cases Finset.mem_insert.mp hpr.2.1 with
          | inl hrq => exact hrq
          | inr hrP =>
            exact False.elim (hd.2 ((native_gap_basis_edge_mem P p r).mpr
              (And.intro hpP (And.intro hrP hpr.2.2))))
        subst r
        exact Finset.mem_image.mpr (Exists.intro p
          (And.intro (Finset.mem_filter.mpr (And.intro hpP hd.1)) rfl))
      case mpr =>
        intro hx
        cases Finset.mem_image.mp hx with
        | intro a ha =>
          have hpq : (a, q) = (p, r) := Sum.inr.inj ha.2
          have hap : a = p := congrArg Prod.fst hpq
          have hqr : q = r := congrArg Prod.snd hpq
          subst a
          subst r
          have hh := Finset.mem_filter.mp ha.1
          apply Finset.mem_erase.mpr
          refine And.intro (by intro h; cases h) ?_
          apply Finset.mem_sdiff.mpr
          refine And.intro hh.2 ?_
          intro hold
          exact hq ((native_gap_basis_edge_mem P p q).mp hold).2.1

theorem native_gap_relation_product_partition (P : Finset Nat)
    (S : Finset (Sum Nat (Prod Nat Nat))) :
    S.prod nativeVertexGapValue =
      (S \ nativeVertexGapBasis P).prod nativeVertexGapValue *
        (Inter.inter S (nativeVertexGapBasis P)).prod nativeVertexGapValue := by
  classical
  have hsub : Inter.inter S (nativeVertexGapBasis P) <= S :=
    Finset.inter_subset_left
  have hd : S \ Inter.inter S (nativeVertexGapBasis P) =
      S \ nativeVertexGapBasis P := by
    ext x
    by_cases hx : Membership.mem S x <;> simp [hx]
  rw [<- Finset.prod_sdiff hsub, hd]

theorem native_gap_new_part_product (P : Finset Nat) (q : Nat)
    (hlarge : forall p : Nat, Membership.mem P p -> p < q)
    (S : Finset (Sum Nat (Prod Nat Nat)))
    (hS : S <= nativeVertexGapBasis (insert q P)) :
    (S \ nativeVertexGapBasis P).prod nativeVertexGapValue =
      (if Membership.mem S (Sum.inl q) then q else 1) *
        (P.filter (fun p => Membership.mem S (Sum.inr (p, q)))).prod
          (fun p => q - p) := by
  classical
  have hpart := native_gap_new_part_erase P q hlarge S hS
  have hinj : Set.InjOn (fun p : Nat => (Sum.inr (p, q) : Sum Nat (Prod Nat Nat)))
      (fun p => Membership.mem (P.filter
        (fun p => Membership.mem S (Sum.inr (p, q)))) p) := by
    intro a _ b _ hab
    exact congrArg Prod.fst (Sum.inr.inj hab)
  have himage : ((P.filter (fun p => Membership.mem S (Sum.inr (p, q)))).image
      (fun p => (Sum.inr (p, q) : Sum Nat (Prod Nat Nat)))).prod nativeVertexGapValue =
      (P.filter (fun p => Membership.mem S (Sum.inr (p, q)))).prod
        (fun p => q - p) := by
    rw [Finset.prod_image hinj]
    rfl
  by_cases hv : Membership.mem S (Sum.inl q)
  case pos =>
    have hvn : Membership.mem (S \ nativeVertexGapBasis P) (Sum.inl q) := by
      apply Finset.mem_sdiff.mpr
      refine And.intro hv ?_
      intro hold
      exact native_gap_new_vertex_not_mem P q hlarge
        ((native_gap_basis_vertex_mem P q).mp hold)
    rw [<- Finset.mul_prod_erase (S \ nativeVertexGapBasis P) nativeVertexGapValue hvn,
      hpart, himage]
    simp [hv, nativeVertexGapValue]
  case neg =>
    have hvn : Not (Membership.mem (S \ nativeVertexGapBasis P) (Sum.inl q)) := by
      intro hx
      exact hv (Finset.mem_sdiff.mp hx).1
    have herase : (S \ nativeVertexGapBasis P).erase (Sum.inl q) =
        S \ nativeVertexGapBasis P := by simp [hvn]
    rw [herase] at hpart
    rw [hpart, himage]
    simp [hv]

theorem native_gap_relation_empty_of_parts (P : Finset Nat) (q : Nat)
    (hlarge : forall p : Nat, Membership.mem P p -> p < q)
    (S : Finset (Sum Nat (Prod Nat Nat)))
    (hS : S <= nativeVertexGapBasis (insert q P))
    (hO : Inter.inter S (nativeVertexGapBasis P) = {})
    (hT : P.filter (fun p => Membership.mem S (Sum.inr (p, q))) = {})
    (hv : Not (Membership.mem S (Sum.inl q))) : S = {} := by
  classical
  refine Finset.Subset.antisymm ?_ (by intro x hx; simp at hx)
  intro x hx
  exfalso
  by_cases hold : Membership.mem (nativeVertexGapBasis P) x
  case pos =>
    have hmem : Membership.mem (Inter.inter S (nativeVertexGapBasis P)) x :=
      Finset.mem_inter.mpr (And.intro hx hold)
    rw [hO] at hmem
    exact Finset.notMem_empty x hmem
  case neg =>
    have hne : Not (x = Sum.inl q) := by
      intro heq
      apply hv
      rw [<- heq]
      exact hx
    have hmem : Membership.mem ((S \ nativeVertexGapBasis P).erase (Sum.inl q)) x :=
      Finset.mem_erase.mpr (And.intro hne (Finset.mem_sdiff.mpr (And.intro hx hold)))
    rw [native_gap_new_part_erase P q hlarge S hS, hT] at hmem
    simp at hmem

end PrimeFactorOscillations.FiniteFieldIntegerSignature
